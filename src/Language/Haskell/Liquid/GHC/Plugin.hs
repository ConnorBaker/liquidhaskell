-- | This module provides a GHC 'Plugin' that allows LiquidHaskell to be hooked directly into GHC's
-- compilation pipeline, facilitating its usage and adoption.

{-# LANGUAGE MultiWayIf                 #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE ViewPatterns               #-}

module Language.Haskell.Liquid.GHC.Plugin (

  plugin

  ) where

import qualified Outputable                              as O
import           GHC                               hiding ( Target
                                                          , Located
                                                          , desugarModule
                                                          )

import qualified GHC                                     as GHC
import           Plugins                                 as GHC
import           TcRnTypes                               as GHC
import           TcRnMonad                               as GHC

import qualified Language.Haskell.Liquid.GHC.Misc        as LH
import qualified Language.Haskell.Liquid.UX.CmdLine      as LH
import qualified Language.Haskell.Liquid.UX.Config       as LH
import qualified Language.Haskell.Liquid.GHC.Interface   as LH
import qualified Language.Haskell.Liquid.Liquid          as LH

import           Language.Haskell.Liquid.GHC.Plugin.Types
import           Language.Haskell.Liquid.GHC.Plugin.Util as Util
import           Language.Haskell.Liquid.GHC.Plugin.SpecFinder
                                                         as SpecFinder

import           Language.Haskell.Liquid.GHC.Types       (MGIModGuts(..), miModGuts)
import qualified Language.Haskell.Liquid.GHC.GhcMonadLike
                                                         as GhcMonadLike
import           Language.Haskell.Liquid.GHC.GhcMonadLike ( GhcMonadLike
                                                          , askHscEnv
                                                          )
import           CoreMonad
import           DataCon
import           DynFlags
import           HscTypes                          hiding ( Target )
import           InstEnv
import           Module
import           FamInstEnv
import qualified TysPrim
import           GHC.LanguageExtensions

import           Control.Monad

import           Data.Coerce
import           Data.List                               as L
                                                   hiding ( intersperse )
import           Data.IORef
import qualified Data.Set                                as S
import           Data.Set                                 ( Set )


import qualified Data.HashSet                            as HS
import qualified Data.HashMap.Strict                     as HM

import           System.Exit
import           System.IO.Unsafe                         ( unsafePerformIO )
import           Language.Fixpoint.Types           hiding ( panic
                                                          , Error
                                                          , Result
                                                          , Expr
                                                          )

import qualified Language.Haskell.Liquid.Measure         as Ms
import           Language.Haskell.Liquid.Parse
import           Language.Haskell.Liquid.Transforms.ANF
import           Language.Haskell.Liquid.Types     hiding ( getConfig )
import           Language.Haskell.Liquid.Bare
import           Language.Haskell.Liquid.UX.CmdLine

import           Optics
import qualified Data.Text.IO as TIO
import qualified Data.Text as T
import Data.Time (getCurrentTime)

import GHC.Paths (libdir)

logPhaseDisk :: Module -> String -> String -> IO ()
logPhaseDisk mdl lbl content = do
  now <- getCurrentTime
  TIO.writeFile (lbl <> "_" <> moduleNameString (moduleName mdl) <> ".log")
                (T.pack content)

---------------------------------------------------------------------------------
-- | State and configuration management -----------------------------------------
---------------------------------------------------------------------------------

-- | A reference to cache the LH's 'Config' and produce it only /once/, during the dynFlags hook.
cfgRef :: IORef Config
cfgRef = unsafePerformIO $ newIORef defConfig
{-# NOINLINE cfgRef #-}

-- | Set to 'True' to enable debug logging.
debugLogs :: Bool
debugLogs = False

---------------------------------------------------------------------------------
-- | Useful functions -----------------------------------------------------------
---------------------------------------------------------------------------------

-- | Reads the 'Config' out of a 'IORef'.
getConfig :: IO Config
getConfig = readIORef cfgRef

-- | Combinator which conditionally print on the screen based on the value of 'debugLogs'.
debugLog :: MonadIO m => String -> m ()
debugLog msg = when debugLogs $ liftIO (putStrLn msg)

---------------------------------------------------------------------------------
-- | The Plugin entrypoint ------------------------------------------------------
---------------------------------------------------------------------------------

plugin :: GHC.Plugin
plugin = GHC.defaultPlugin {
    parsedResultAction    = \_ _ pm -> pure pm
  , typeCheckResultAction = typecheckHook
  , installCoreToDos      = coreHook
  , dynflagsPlugin        = customDynFlags
  , pluginRecompile       = \_ -> pure NoForceRecompile
  , interfaceLoadAction   = loadInterfaceHook
  }

--------------------------------------------------------------------------------
-- | GHC Configuration & Setup -------------------------------------------------
--------------------------------------------------------------------------------

-- | Overrides the default 'DynFlags' options. Specifically, we need the GHC
-- lexer not to throw away block comments, as this is where the LH spec comments
-- would live. This is why we set the 'Opt_KeepRawTokenStream' option.
customDynFlags :: [CommandLineOption] -> DynFlags -> IO DynFlags
customDynFlags opts dflags = do
  cfg <- liftIO $ LH.getOpts opts
  writeIORef cfgRef cfg
  configureDynFlags dflags

configureDynFlags :: DynFlags -> IO DynFlags
configureDynFlags df =
  pure $ df `gopt_set` Opt_ImplicitImportQualified
            `gopt_set` Opt_PIC
            `gopt_set` Opt_DeferTypedHoles
            `gopt_set` Opt_KeepRawTokenStream
            `xopt_set` MagicHash
            `xopt_set` DeriveGeneric
            `xopt_set` StandaloneDeriving

--------------------------------------------------------------------------------
-- | Parsing phase -------------------------------------------------------------
--------------------------------------------------------------------------------

-- | Hook into the parsing phase and extract \"LiquidHaskell\"'s spec comments, turning them into
-- module declarations (i.e. 'LhsDecl GhcPs') which can be later be consumed in the typechecking phase.
-- The goal for this phase is /not/ to turn spec comments into a fully-fledged data structure, but rather
-- carry those string fragments (together with their 'SourcePos') into the next phase.
    {-
parseHook :: [CommandLineOption]
          -> ModSummary
          -> HsParsedModule
          -> Hsc HsParsedModule
parseHook _ (unoptimise -> modSummary) parsedModule = do
  -- NOTE: Be careful with the ordering of 'SpecComment's, because in the plugin infrastructure
  -- if those would appear in a different order than what LiquidHaskell expects, the parser would choke,
  -- as the latter is stateful with regards to the infix operators.
  let comments  = LH.extractSpecComments (hpm_annotations parsedModule)

  -- Run 'parseModule' with a \"cleaned\" 'ModSummary'. We need this to avoid entering in an endless loop when
  -- the LiquidHaskell plugin code runs via GHCi. The culprit seems to be the definition of 'parseModule',
  -- which calls 'hscParse', and the latter has these lines at the end:
  --
  --    -- apply parse transformation of plugins
  --    let applyPluginAction p opts
  --          = parsedResultAction p opts mod_summary
  --    withPlugins dflags applyPluginAction res
  --
  -- This seems to suggest we call any plugin-registered parsing hooks, including ours (!!), leading to
  -- a loop, albeit it's unclear why this does not happen for non-interactive GHC. What we do here, instead,
  -- is to clean all the plugins from the 'DynFlags' we use in the sandbox, so that we break the recursion.
  parsed <- GhcMonadLike.parseModule (LH.keepRawTokenStream cleanedSummary)

  -- Calling 'typecheckModule' here will load some interfaces which won't be re-opened by the
  -- 'loadInterfaceAction'. Therefore it's necessary we do all the lookups for necessary specs elsewhere
  -- (i.e., here).
  typechecked     <- GhcMonadLike.typecheckModule (LH.ignoreInline parsed)

  -- \"The ugly hack\": grab the unoptimised core binds here.
  unoptimisedGuts <- GhcMonadLike.desugarModule modSummary typechecked

  -- Resolve names and imports
  env <- askHscEnv
  resolvedNames <- LH.lookupTyThings env (GhcMonadLike.tm_mod_summary typechecked)
                                         (GhcMonadLike.tm_gbl_env typechecked)
  availTyCons   <- LH.availableTyCons env (GhcMonadLike.tm_mod_summary typechecked)
                                          (GhcMonadLike.tm_gbl_env typechecked)
                                          (tcg_exports $ GhcMonadLike.tm_gbl_env typechecked)
  availVars     <- LH.availableVars env (GhcMonadLike.tm_mod_summary typechecked)
                                        (GhcMonadLike.tm_gbl_env typechecked)
                                        (tcg_exports $ GhcMonadLike.tm_gbl_env typechecked)

  let tcData       = mkTcData typechecked resolvedNames availTyCons availVars
  let pipelineData = PipelineData (toUnoptimised unoptimisedGuts) tcData (map SpecComment comments)

  debugLog $ "Resolved names:\n" ++ (O.showSDocUnsafe $ O.ppr resolvedNames)
  debugLog $ "Optimised Core:\n" ++ (O.showSDocUnsafe $ O.ppr (mg_binds unoptimisedGuts))
  debugLog $ "Spec comments: "   ++ show comments

  pure parsedModule

  where
    thisModule :: Module
    thisModule = ms_mod modSummary

    cleanedSummary :: ModSummary
    cleanedSummary = modSummary { ms_hspp_opts = (ms_hspp_opts modSummary) { cachedPlugins = []
                                                                           , staticPlugins = []
                                                                           }
                                }
-}

--------------------------------------------------------------------------------
-- | \"Unoptimising\" things ----------------------------------------------------
--------------------------------------------------------------------------------

-- | LiquidHaskell requires the unoptimised core binds in order to work correctly, but at the same time the
-- user can invoke GHC with /any/ optimisation flag turned out. This is why we grab the core binds by
-- desugaring the module during /parsing/ (before that's already too late) and we cache the core binds for
-- the rest of the program execution.
class Unoptimise a where
  type UnoptimisedTarget a :: *
  unoptimise :: a -> UnoptimisedTarget a

instance Unoptimise DynFlags where
  type UnoptimisedTarget DynFlags = DynFlags
  unoptimise df = updOptLevel 0 df
    { debugLevel   = 1
    , ghcLink      = LinkInMemory
    , hscTarget    = HscInterpreted
    , ghcMode      = CompManager
    }

instance Unoptimise ModSummary where
  type UnoptimisedTarget ModSummary = ModSummary
  unoptimise modSummary = modSummary { ms_hspp_opts = unoptimise (ms_hspp_opts modSummary) }

instance Unoptimise (DynFlags, HscEnv) where
  type UnoptimisedTarget (DynFlags, HscEnv) = HscEnv
  unoptimise (unoptimise -> df, env) = env { hsc_dflags = df }

--------------------------------------------------------------------------------
-- | Typechecking phase --------------------------------------------------------
--------------------------------------------------------------------------------

-- | We hook at this stage of the pipeline in order to call \"liquidhaskell\". This
-- might seems counterintuitive as LH works on a desugared module. However, there
-- are a bunch of reasons why we do this:
-- 1. Tools like \"ghcide\" works by running the compilation pipeline up until
--    this stage, which means that we won't be able to report errors and warnings
--    if we call /LH/ any later than here;
--
-- 2. Although /LH/ works on \"Core\", it requires the _unoptimised_ \"Core\" that we
--    grab from the parsing phase and we thread it across the entire plugin lifecycle.
typecheckHook :: [CommandLineOption] -> ModSummary -> TcGblEnv -> TcM TcGblEnv
typecheckHook _ (unoptimise -> modSummary) tcGblEnv = do
  dynFlags <- getDynFlags
  cfg <- liftIO getConfig

  oldEnv <- askHscEnv
  pipelineData <- runGhcT (Just libdir) $ do
    setSession oldEnv
    parsed <- GHC.parseModule (LH.keepRawTokenStream cleanedSummary)
    let comments  = LH.extractSpecComments (pm_annotations parsed)
    --liftIO $ logPhaseDisk thisModule "typecheckHook.before_typechecked" mempty
    typechecked     <- GHC.typecheckModule (LH.ignoreInline parsed)
    --liftIO $ logPhaseDisk thisModule "typecheckHook.after_typechecked" mempty

    unoptimisedGuts <- dm_core_module <$> GHC.desugarModule typechecked

    env <- getSession

    resolvedNames <- LH.lookupTyThings env (pm_mod_summary parsed)
                                           (fst . tm_internals_ $ typechecked)
    availTyCons   <- LH.availableTyCons env (pm_mod_summary parsed)
                                            (fst . tm_internals_ $ typechecked)
                                            (tcg_exports . fst . tm_internals_ $ typechecked)
    availVars     <- LH.availableVars env (pm_mod_summary parsed)
                                          (fst . tm_internals_ $ typechecked)
                                          (tcg_exports . fst . tm_internals_ $ typechecked)

    let tcData       = mkTcData (tm_renamed_source typechecked) resolvedNames availTyCons availVars
    pure $ PipelineData (toUnoptimised unoptimisedGuts) tcData (map SpecComment comments)


  liquidHaskellCheck cfg pipelineData tcGblEnv
  where
    thisModule :: Module
    thisModule = tcg_mod tcGblEnv

    cleanedSummary :: ModSummary
    cleanedSummary =
        modSummary { ms_hspp_opts = (ms_hspp_opts modSummary) { cachedPlugins = []
                                                              , staticPlugins = []
                                                              }
                   }


-- | Partially calls into LiquidHaskell's GHC API.
liquidHaskellCheck :: LH.Config -> PipelineData -> TcGblEnv -> TcM TcGblEnv
liquidHaskellCheck cfg pipelineData tcGblEnv = do

  -- liftIO $ logPhaseDisk thisModule "liquidHaskellCheck" mempty

  let specQuotes = LH.extractSpecQuotes' tcg_mod tcg_anns tcGblEnv
  inputSpec <- getLiquidSpec thisModule (pdSpecComments pipelineData) specQuotes

  debugLog $ " Input spec: \n" ++ show inputSpec

  modSummary <- GhcMonadLike.getModSummary (moduleName thisModule)
  dynFlags <- getDynFlags

  debugLog $ "Relevant ===> \n" ++ (unlines $ map renderModule $ (S.toList $ relevantModules modGuts))

  logicMap <- liftIO $ LH.makeLogicMap

  let lhContext = LiquidHaskellContext {
        lhGlobalCfg       = cfg
      , lhInputSpec       = inputSpec
      , lhModuleLogicMap  = logicMap
      , lhModuleSummary   = modSummary
      , lhModuleTcData    = pdTcData pipelineData
      , lhModuleGuts      = pdUnoptimisedCore pipelineData
      , lhRelevantModules = relevantModules modGuts
      }

  ProcessModuleResult{..} <- processModule lhContext

  -- Call into the existing Liquid interface
  out <- liftIO $ LH.checkTargetInfo pmrTargetInfo
  -- despite the name, 'exitWithResult' simply print on stdout extra info.
  void . liftIO $ LH.exitWithResult dynFlags cfg [giTarget (giSrc pmrTargetInfo)] out
  case o_result out of
    Safe _stats -> pure ()
    _           -> liftIO exitFailure

  let serialisedSpec = Util.serialiseLiquidLib pmrClientLib thisModule
  debugLog $ "Serialised annotation ==> " ++ (O.showSDocUnsafe . O.ppr $ serialisedSpec)

  pure $ tcGblEnv { tcg_anns = serialisedSpec : tcg_anns tcGblEnv }
  where
    thisModule :: Module
    thisModule = tcg_mod tcGblEnv

    modGuts :: ModGuts
    modGuts = fromUnoptimised . pdUnoptimisedCore $ pipelineData


--------------------------------------------------------------------------------
-- | Working with bare & lifted specs ------------------------------------------
--------------------------------------------------------------------------------

loadDependencies :: forall m. GhcMonadLike m
                 => Config
                 -- ^ The 'Config' associated to the /current/ module being compiled.
                 -> ExternalPackageState
                 -> HomePackageTable
                 -> Module
                 -> [Module]
                 -> m TargetDependencies
loadDependencies currentModuleConfig eps hpt thisModule mods = do
  results   <- SpecFinder.findRelevantSpecs eps hpt mods
  deps      <- foldlM processResult mempty (reverse results)
  redundant <- configToRedundantDependencies currentModuleConfig

  debugLog $ "Redundant dependencies ==> " ++ show redundant

  pure $ foldl' (flip dropDependency) deps redundant
  where
    processResult :: TargetDependencies -> SpecFinderResult -> m TargetDependencies
    processResult !acc (SpecNotFound mdl) = do
      debugLog $ "[T:" ++ renderModule thisModule
              ++ "] Spec not found for " ++ renderModule mdl
      pure acc
    processResult _ (SpecFound originalModule location _) = do
      dynFlags <- getDynFlags
      debugLog $ "[T:" ++ show (moduleName thisModule)
              ++ "] Spec found for " ++ renderModule originalModule ++ ", at location " ++ show location
      Util.pluginAbort (O.showSDoc dynFlags $ O.text "A BareSpec was returned as a dependency, this is not allowed, in " O.<+> O.ppr thisModule)
    processResult !acc (LibFound originalModule location lib) = do
      debugLog $ "[T:" ++ show (moduleName thisModule)
              ++ "] Lib found for " ++ renderModule originalModule ++ ", at location " ++ show location
      pure $ TargetDependencies {
          getDependencies = HM.insert (toStableModule originalModule) (libTarget lib) (getDependencies $ acc <> libDeps lib)
        }

-- | The collection of dependencies and usages modules which are relevant for liquidHaskell
relevantModules :: ModGuts -> Set Module
relevantModules modGuts = used `S.union` dependencies
  where
    dependencies :: Set Module
    dependencies = S.fromList $ map (toModule . fst) . filter (not . snd) . dep_mods $ deps

    deps :: Dependencies
    deps = mg_deps modGuts

    thisModule :: Module
    thisModule = mg_module modGuts

    toModule :: ModuleName -> Module
    toModule = Module (moduleUnitId thisModule)

    used :: Set Module
    used = S.fromList $ foldl' collectUsage mempty . mg_usages $ modGuts
      where
        collectUsage :: [Module] -> Usage -> [Module]
        collectUsage acc = \case
          UsagePackageModule     { usg_mod      = modl    } -> modl : acc
          UsageHomeModule        { usg_mod_name = modName } -> toModule modName : acc
          UsageMergedRequirement { usg_mod      = modl    } -> modl : acc
          _ -> acc


data LiquidHaskellContext = LiquidHaskellContext {
    lhGlobalCfg        :: Config
  , lhInputSpec        :: BareSpec
  , lhModuleLogicMap   :: LogicMap
  , lhModuleSummary    :: ModSummary
  , lhModuleTcData     :: TcData
  , lhModuleGuts       :: Unoptimised ModGuts
  , lhRelevantModules  :: Set Module
  }

--------------------------------------------------------------------------------
-- | Per-Module Pipeline -------------------------------------------------------
--------------------------------------------------------------------------------

data ProcessModuleResult = ProcessModuleResult {
    pmrClientLib  :: LiquidLib
  -- ^ The \"client library\" we will serialise on disk into an interface's 'Annotation'.
  , pmrTargetInfo :: TargetInfo
  -- ^ The 'GhcInfo' for the current 'Module' that LiquidHaskell will process.
  }

getLiquidSpec :: GhcMonadLike m => Module -> [SpecComment] -> [BPspec] -> m BareSpec
getLiquidSpec thisModule specComments specQuotes = do

  let commSpecE = hsSpecificationP (moduleName thisModule) (coerce specComments) specQuotes
  case commSpecE of
    Left errors -> do
      dynFlags <- getDynFlags
      liftIO $ do
        mapM_ (printError Full dynFlags) errors
        exitFailure
    Right (view bareSpecIso . snd -> commSpec) -> do
      res <- SpecFinder.findCompanionSpec thisModule
      case res of
        SpecFound _ _ companionSpec -> do
          debugLog $ "Companion spec found for " ++ renderModule thisModule
          pure $ commSpec <> companionSpec
        _ -> pure commSpec

processModule :: GhcMonadLike m => LiquidHaskellContext -> m ProcessModuleResult
processModule LiquidHaskellContext{..} = do
  debugLog ("Module ==> " ++ renderModule thisModule)
  hscEnv              <- askHscEnv

  let bareSpec        = lhInputSpec
  -- /NOTE/: For the Plugin to work correctly, we shouldn't call 'canonicalizePath', because otherwise
  -- this won't trigger the \"external name resolution\" as part of 'Language.Haskell.Liquid.Bare.Resolve'
  -- (cfr. 'allowExtResolution').
  let file            = LH.modSummaryHsFile lhModuleSummary

  _                   <- LH.checkFilePragmas $ Ms.pragmas (review bareSpecIso bareSpec)

  moduleCfg           <- liftIO $ withPragmas lhGlobalCfg file (Ms.pragmas $ review bareSpecIso bareSpec)
  eps                 <- liftIO $ readIORef (hsc_EPS hscEnv)

  dependencies       <- loadDependencies moduleCfg
                                         eps
                                         (hsc_HPT hscEnv)
                                         thisModule
                                         (S.toList lhRelevantModules)

  debugLog $ "Found " <> show (HM.size $ getDependencies dependencies) <> " dependencies:"
  when debugLogs $
    forM_ (HM.keys . getDependencies $ dependencies) $ debugLog . moduleStableString . unStableModule

  debugLog $ "mg_exports => " ++ (O.showSDocUnsafe $ O.ppr $ mg_exports modGuts)
  debugLog $ "mg_tcs => " ++ (O.showSDocUnsafe $ O.ppr $ mg_tcs modGuts)

  targetSrc  <- makeTargetSrc moduleCfg file lhModuleTcData modGuts hscEnv
  dynFlags <- getDynFlags

  case makeTargetSpec moduleCfg lhModuleLogicMap targetSrc bareSpec dependencies of

    -- Print warnings and errors, aborting the compilation.
    Left diagnostics -> do
      liftIO $ do
        mapM_ (printWarning dynFlags)    (allWarnings diagnostics)
        mapM_ (printError Full dynFlags) (allErrors diagnostics)
        exitFailure

    Right (warnings, targetSpec, liftedSpec) -> do
      liftIO $ mapM_ (printWarning dynFlags) warnings
      let targetInfo = TargetInfo targetSrc targetSpec

      debugLog $ "bareSpec ==> "   ++ show bareSpec
      debugLog $ "liftedSpec ==> " ++ show liftedSpec

      let clientLib  = mkLiquidLib liftedSpec & addLibDependencies dependencies

      let result = ProcessModuleResult {
            pmrClientLib  = clientLib
          , pmrTargetInfo = targetInfo
          }

      pure result

  where
    modGuts    = fromUnoptimised lhModuleGuts
    thisModule = mg_module modGuts

---------------------------------------------------------------------------------------
-- | @makeGhcSrc@ builds all the source-related information needed for consgen
---------------------------------------------------------------------------------------

makeTargetSrc :: GhcMonadLike m
              => Config
              -> FilePath
              -> TcData
              -> ModGuts
              -> HscEnv
              -> m TargetSrc
makeTargetSrc cfg file tcData modGuts hscEnv = do
  coreBinds      <- liftIO $ anormalize cfg hscEnv modGuts

  -- The type constructors for a module are the (nubbed) union of the ones defined and
  -- the ones exported. This covers the case of \"wrapper modules\" that simply re-exports
  -- everything from the imported modules.
  let availTcs    = tcAvailableTyCons tcData
  let allTcs      = L.nub $ (mgi_tcs mgiModGuts ++ availTcs)

  let dataCons       = concatMap (map dataConWorkId . tyConDataCons) allTcs
  let (fiTcs, fiDcs) = LH.makeFamInstEnv (getFamInstances modGuts)
  let things         = tcResolvedNames tcData
  let impVars        = LH.importVars coreBinds ++ LH.classCons (mgi_cls_inst mgiModGuts)

  debugLog $ "_gsTcs   => " ++ show allTcs
  debugLog $ "_gsFiTcs => " ++ show fiTcs
  debugLog $ "_gsFiDcs => " ++ show fiDcs
  debugLog $ "dataCons => " ++ show dataCons
  debugLog $ "defVars  => " ++ show (L.nub $ dataCons ++ (letVars coreBinds) ++ tcAvailableVars tcData)

  return $ TargetSrc
    { giIncDir    = mempty
    , giTarget    = file
    , giTargetMod = ModName Target (moduleName (mg_module modGuts))
    , giCbs       = coreBinds
    , giImpVars   = impVars
    , giDefVars   = L.nub $ dataCons ++ (letVars coreBinds) ++ tcAvailableVars tcData
    , giUseVars   = readVars coreBinds
    , giDerVars   = HS.fromList (LH.derivedVars cfg mgiModGuts)
    , gsExports   = mgi_exports  mgiModGuts
    , gsTcs       = allTcs
    , gsCls       = mgi_cls_inst mgiModGuts
    , gsFiTcs     = fiTcs
    , gsFiDcs     = fiDcs
    , gsPrimTcs   = TysPrim.primTyCons
    , gsQualImps  = tcQualifiedImports tcData
    , gsAllImps   = tcAllImports       tcData
    , gsTyThings  = [ t | (_, Just t) <- things ]
    }
  where
    mgiModGuts :: MGIModGuts
    mgiModGuts = miModGuts deriv modGuts
      where
        deriv   = Just $ instEnvElts $ mg_inst_env modGuts

getFamInstances :: ModGuts -> [FamInst]
getFamInstances guts = famInstEnvElts (mg_fam_inst_env guts)

---------------------------------------------------------------------------------
-- | Unused stages of the compilation pipeline ----------------------------------
---------------------------------------------------------------------------------

coreHook :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
coreHook _ passes = pure passes

loadInterfaceHook :: [CommandLineOption] -> ModIface -> IfM lcl ModIface
loadInterfaceHook _ iface = pure iface
