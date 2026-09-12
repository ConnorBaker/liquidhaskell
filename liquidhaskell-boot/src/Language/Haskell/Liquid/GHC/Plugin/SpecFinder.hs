{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes   #-}

{-
Note [Module Visibility and Lookup in GHC]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
GHC distinguishes between two module visibility namespaces:

- **Regular packages** (`-package`): modules are found by `findImportedModule`,
  which searches `findExposedPackageModule`.
- **Plugin packages** (`-plugin-package`): modules are found by
  `findPluginModule`, which searches `findExposedPluginPackageModule`.

Whenever a module is looked up, we start with `findImportedModule` to check
regular packages, and if that fails, we fall back to `findPluginModule` to check
plugin packages. This allows us to support both visibility namespaces without
requiring users to mind how they specify dependencies.

-}

module Language.Haskell.Liquid.GHC.Plugin.SpecFinder
    ( findRelevantSpecs
    , findTotalitySpec
    , SpecFinderResult(..)
    , configToRedundantDependencies
    ) where

import qualified Language.Haskell.Liquid.GHC.Plugin.Serialisation as Serialisation
import           Language.Haskell.Liquid.GHC.Plugin.Types
import           Language.Haskell.Liquid.UX.Config

import           Liquid.GHC.API         as GHC
import           GHC.Data.Maybe (MaybeErr (..))
import           GHC.Driver.Env (hsc_HUG)
import           GHC.Driver.Session (ghcMode, isOneShot)
import qualified GHC.Unit.Home.Graph as HUG
import           GHC.Unit.Module (getModuleInstantiation)

import           Data.Bifunctor
import qualified Data.Char
import           Data.IORef
import           Data.Maybe

import           Control.Monad.Trans.Maybe


type SpecFinder m = Module -> MaybeT IO SpecFinderResult

-- | The result of searching for a spec.
data SpecFinderResult =
    SpecNotFound Module
  | LibFound Module LiquidLib

-- | Load any relevant spec for the input list of 'Module's, by querying both the 'ExternalPackageState'
-- and the 'HomePackageTable'.
--
-- Specs come from the interface files of the given modules or their matching
-- _LHAssumptions modules. A module @M@ only matches with a module named
-- @M_LHAssumptions@.
--
-- Assumptions are taken from _LHAssumptions modules only if the interface
-- file of the matching module contains no spec.
findRelevantSpecs :: [String] -- ^ Package to exclude for loading LHAssumptions
                  -> HscEnv
                  -> [Module]
                  -- ^ Any relevant module fetched during dependency-discovery.
                  -> TcM [SpecFinderResult]
findRelevantSpecs lhAssmPkgExcludes hscEnv mods = do
    eps <- liftIO $ readIORef (euc_eps $ ue_eps $ hsc_unit_env hscEnv)
    mapM (loadRelevantSpec eps) mods
  where

    loadRelevantSpec :: ExternalPackageState -> Module -> TcM SpecFinderResult
    loadRelevantSpec eps currentModule = do
      res <- liftIO $ runMaybeT $
        lookupInterfaceAnnotations hscEnv eps (hsc_NC hscEnv) currentModule
      case res of
        Nothing         -> do
          mAssm <- loadModuleLHAssumptionsIfAny currentModule
          return $ fromMaybe (SpecNotFound currentModule) mAssm
        Just specResult ->
          return specResult

    loadModuleLHAssumptionsIfAny m | isImportExcluded m = return Nothing
                                   | otherwise = do
      let assumptionsModName = assumptionsModuleName m
      -- loadInterface might mutate the EPS if the module is
      -- not already loaded.
      --
      -- Try findImportedModule first (for -package), then fall back to
      -- findPluginModule (for -plugin-package).
      -- See Note [Module Visibility and Lookup in GHC] for details.
      res <- liftIO $ do
        r <- findImportedModule hscEnv assumptionsModName NoPkgQual
        case r of
          Found{} -> pure r
          _       -> findPluginModule hscEnv assumptionsModName
      case res of
        Found _ assumptionsMod -> do
          -- Mirror GHC.Iface.Load's HomeModError boundary before loading:
          -- an optional future/self home module has no completed interface.
          -- Calling loadInterface here would cache an empty failed interface
          -- in the EPS, making subsequent discovery mistake it for a load.
          homeInfo <- liftIO $ HUG.lookupHugByModule assumptionsMod (hsc_HUG hscEnv)
          let installedMod = fst $ getModuleInstantiation assumptionsMod
              unavailableHome =
                HUG.memberHugUnitId (moduleUnit installedMod) (hsc_HUG hscEnv)
                && not (isOneShot (ghcMode $ hsc_dflags hscEnv))
                && isNothing homeInfo
          if unavailableHome then pure Nothing else do
            loaded <- initIfaceTcRn $ loadInterface "liquidhaskell assumptions" assumptionsMod ImportBySystem
            case loaded of
              Failed err -> failWithTc $ mkTcRnUnknownMessage $ mkPlainError [] $
                missingInterfaceErrorDiagnostic (initIfaceMessageOpts $ hsc_dflags hscEnv) err
              Succeeded _ -> do
                eps2 <- liftIO $ readIORef (euc_eps $ ue_eps $ hsc_unit_env hscEnv)
                liftIO $ runMaybeT $ lookupInterfaceAnnotations hscEnv eps2 (hsc_NC hscEnv) assumptionsMod
        FoundMultiple{} -> failWithTc $ mkTcRnUnknownMessage $ mkPlainError [] $
                             missingInterfaceErrorDiagnostic (initIfaceMessageOpts $ hsc_dflags hscEnv) $
                             cannotFindModule hscEnv assumptionsModName res
        _ -> return Nothing

    isImportExcluded m =
      let s = takeWhile Data.Char.isAlphaNum $ unitString (moduleUnit m)
       in elem s lhAssmPkgExcludes

    assumptionsModuleName m =
      mkModuleNameFS $ moduleNameFS (moduleName m) <> "_LHAssumptions"

-- | Load specs from an interface file.
lookupInterfaceAnnotations :: HscEnv -> ExternalPackageState -> NameCache -> SpecFinder m
lookupInterfaceAnnotations env eps nameCache thisModule = do
  lib <- MaybeT $ Serialisation.deserialiseLiquidLib env thisModule eps nameCache
  pure $ LibFound thisModule lib

-- | Totality is a checking policy, not a property of importing Prelude.
-- A NoImplicitPrelude client can obtain a partial primitive through any
-- reexport, including a facade compiled without LH annotations. Load the
-- existing policy independently of those imports; do not duplicate its specs.
findTotalitySpec :: HscEnv -> Config -> TcM [SpecFinderResult]
findTotalitySpec env cfg
  | not (totalityCheck cfg) = pure []
  | otherwise = do
      flags <- getDynFlags
      -- Only the package that builds the assumptions may bootstrap without
      -- them. An application using LiquidHaskellBoot directly must not
      -- silently lose the selected totality policy.
      if thisPackageName flags == Just "liquidhaskell"
        then pure []
        else do
          policyModule <- liftIO $ lookupLiquidBaseModule env totalityModuleName
          case policyModule of
            Just mdl -> do
              loaded <- initIfaceTcRn $ loadInterface "liquidhaskell totality policy" mdl ImportBySystem
              case loaded of
                Failed err -> failWithTc $ mkTcRnUnknownMessage $ mkPlainError [] $
                  missingInterfaceErrorDiagnostic (initIfaceMessageOpts $ hsc_dflags env) err
                Succeeded _ -> pure ()
              eps <- liftIO $ readIORef (euc_eps $ ue_eps $ hsc_unit_env env)
              spec <- liftIO $ runMaybeT $
                lookupInterfaceAnnotations env eps (hsc_NC env) mdl
              case spec of
                Just found -> pure [found]
                Nothing -> missingPolicy
            Nothing -> missingPolicy
  where
    missingPolicy = failWithTc $ mkTcRnUnknownMessage $ mkPlainError [] $
      text "LiquidHaskell totality policy is unavailable; expose the liquidhaskell package with its compiled LH assumptions."

totalityModuleName :: ModuleName
totalityModuleName = mkModuleName "Liquid.Prelude.Totality_LHAssumptions"

lookupLiquidBaseModule :: HscEnv -> ModuleName -> IO (Maybe Module)
lookupLiquidBaseModule env mn = do
  res <- findImportedModule env mn (renamePkgQual (hsc_unit_env env) mn (Just "liquidhaskell"))
  case res of
    Found _ mdl -> pure $ Just mdl
    _ -> do
      -- Plugin packages occupy a separate visibility namespace.
      res2 <- findPluginModule env mn
      case res2 of
        Found _ mdl -> pure $ Just mdl
        _           -> pure Nothing

-- | Returns a list of 'StableModule's which can be filtered out of the dependency list, because they are
-- selectively \"toggled\" on and off by the LiquidHaskell's configuration, which granularity can be
-- /per module/.
configToRedundantDependencies :: HscEnv -> Config -> IO [StableModule]
configToRedundantDependencies env cfg = do
  catMaybes <$> mapM (lookupModule' . first ($ cfg)) configSensitiveDependencies
  where
    lookupModule' :: (Bool, ModuleName) -> IO (Maybe StableModule)
    lookupModule' (fetchModule, modName)
      | fetchModule = fmap toStableModule <$> lookupLiquidBaseModule env modName
      | otherwise   = pure Nothing

-- | Static associative map of the 'ModuleName' that needs to be filtered from the final 'TargetDependencies'
-- due to some particular configuration options.
--
-- Modify this map to add any extra special case. Remember that the semantic is not which module will be
-- /added/, but rather which one will be /removed/ from the final list of dependencies.
--
configSensitiveDependencies :: [(Config -> Bool, ModuleName)]
configSensitiveDependencies = [
    (not . totalityCheck, totalityModuleName)
  , (linear, mkModuleName "Liquid.Prelude.Real_LHAssumptions")
  ]
