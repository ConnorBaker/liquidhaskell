{-# LANGUAGE OverloadedStrings #-}

module CachedNativePrefixTests (tests) where

import Control.DeepSeq (rnf)
import Control.Exception (SomeException, evaluate, try)
import Control.Monad (void)
import Control.Monad.State (runState)
import qualified Data.HashSet as S
import GHC.Unit.Module (mkModule, mkModuleName)
import GHC.Unit.Types (stringToUnit)
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Constraint.Env (toListREnv)
import Language.Haskell.Liquid.Constraint.Generate (ConstraintObligations (..), generateConstraints)
import Language.Haskell.Liquid.Constraint.Init (DefaultTypes, initCGI, initEnv, prepareDefaultTypes)
import Language.Haskell.Liquid.Constraint.Qualifier (giQuals)
import Language.Haskell.Liquid.Constraint.ToFixpoint (cgInfoFInfo)
import qualified Language.Haskell.Liquid.Constraint.Types as CG
import qualified Language.Haskell.Liquid.Types.Fresh as Fresh
import Language.Haskell.Liquid.Types.Names (getPropIndex, lhNameToResolvedSymbol, makeLogicLHName)
import Language.Haskell.Liquid.Types.RType (SpecType, TyConP (..), szFun)
import Language.Haskell.Liquid.Types.RefType (addTyConInfo, ofType)
import Language.Haskell.Liquid.Types.Specs
import Language.Haskell.Liquid.Types.Types (MeasureKind (MsAbsMeasure), MeasureV (..))
import Language.Haskell.Liquid.Types.Visitors (freeVars)
import Language.Haskell.Liquid.UX.CmdLine (defConfig)
import qualified Language.Haskell.Liquid.UX.Config as LH
import Language.Haskell.Liquid.WiredIn (wiredTyCons)
import qualified Liquid.GHC.API as G
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))

tests :: (LH.Config -> TargetInfo) -> (String -> String -> IO G.CoreProgram) -> TestTree
tests makeEmpty compileToCore =
    testGroup
        "cached native prefix"
        [ testGroup
            "autosize declaration ownership"
            [ testCase "uses actual first-unit declaration" $ observe [first] [first] @?= Just (project first)
            , testCase "uses actual second-unit declaration" $ observe [second] [second] @?= Just (project second)
            , testCase "same module in distinct units is ambiguous" $ observe [first, second] [first, second] @?= Nothing
            , testCase "unregistered declaration cannot supply generated calls" $ observe [first] [] @?= Nothing
            , testCase "unrelated authored occurrence is not the qualified declaration" $ observe [unrelated] [unrelated] @?= Nothing
            , testCase "wired list metric uses the selected declaration owner" $
                listMetric (Just (F.dummyLoc listSizeOwner)) @?= Just (F.mkEApp (F.dummyLoc listSizeOwner) [F.EVar "value"])
            , testCase "absent list measure supplies no inferred metric" $ listMetric Nothing @?= Nothing
            , testCase "proposition index uses its selected actual owner" $ getPropIndex (Just firstSymbol) (indexed firstSymbol) @?= Just index
            , testCase "same displayed name in another unit is not that index owner" $ getPropIndex (Just firstSymbol) (indexed secondSymbol) @?= Nothing
            , testCase "absent declaration licenses no proposition index" $ getPropIndex Nothing (indexed firstSymbol) @?= Nothing
            ]
        , testGroup
            "complete constraint generation"
            [ testCase (show (allow, seed)) (fullComparison allow seed)
            | allow <- [False, True]
            , seed <- [0, 17, 103]
            ]
        , testGroup
            "lazy state observations"
            [ testCase (show (bottomSeed, poisonedTail, countOnly)) $
                void $
                    demandComparison (G.dataConWorkId G.trueDataCon) bottomSeed poisonedTail $
                        if countOnly then snd else \((rows, _, _), _) -> toInteger (length (take 1 rows))
            | bottomSeed <- [False, True]
            , poisonedTail <- [False, True]
            , countOnly <- [False, True]
            ]
        , testCase "observing an arrow binder demands its fresh seed" $ do
            program <-
                compileToCore "NativePrefixDemandArrow" $
                    unlines
                        [ "module NativePrefixDemandArrow where"
                        , "identity :: Bool -> Bool"
                        , "identity x = x"
                        ]
            case [owner | (owner, _) <- G.flattenBinds program, G.getOccString owner == "identity"] of
                [owner] -> do
                    defined <- demandComparison owner True False $ \((rows, _, _), _) ->
                        toInteger (sum [length (F.showpp ty) | (_, ty) <- rows])
                    assertBool "arrow binder observation must demand the bottom seed" (not defined)
                _ -> assertBool "expected one actual arrow owner" False
        ]
  where
    empty = makeEmpty defConfig
    first = makeLogicLHName "autolen" (mkModule (stringToUnit "first-unit") (mkModuleName "GHC.Base_LHAssumptions")) Nothing
    second = makeLogicLHName "autolen" (mkModule (stringToUnit "second-unit") (mkModuleName "GHC.Base_LHAssumptions")) Nothing
    unrelated = makeLogicLHName "autolen" (mkModule (stringToUnit "first-unit") (mkModuleName "Other")) Nothing
    project = F.dummyLoc . lhNameToResolvedSymbol
    listSizeOwner = lhNameToResolvedSymbol (makeLogicLHName "len" (mkModule (stringToUnit "first-unit") (mkModuleName "GHC.Types_LHAssumptions")) Nothing)
    firstSymbol = lhNameToResolvedSymbol (makeLogicLHName "prop" (mkModule (stringToUnit "first-unit") (mkModuleName "Language.Haskell.Liquid.ProofCombinators")) Nothing)
    secondSymbol = lhNameToResolvedSymbol (makeLogicLHName "prop" (mkModule (stringToUnit "second-unit") (mkModuleName "Language.Haskell.Liquid.ProofCombinators")) Nothing)
    index = F.ECon (F.I 0)
    indexed owner = F.Reft ("value", F.PAtom F.Eq (F.EApp (F.EVar owner) (F.EVar "value")) index)
    listMetric owner = case [tcpSizeFun ty | ty <- wiredTyCons owner, tcpCon ty == G.listTyCon] of
        [metric] -> (\f -> szFun f "value") <$> metric
        _ -> error "expected one wired list declaration"
    observe declarations registered =
        autoSizeMeasure $
            (giSpec empty)
                { gsData =
                    (gsData (giSpec empty))
                        { gsMeasures = [M (F.dummyLoc owner) scalar [] MsAbsMeasure [] | owner <- declarations]
                        , gsMeas = [(lhNameToResolvedSymbol owner, F.dummyLoc scalar) | owner <- registered]
                        }
                }
    scalar = ofType G.boolTy
    fullComparison allow seed = do
        allCore <-
            compileToCore "NativePrefixActual" $
                unlines
                    [ "module NativePrefixActual where"
                    , "import Prelude (Bool(..), id)"
                    , "poly :: (Bool -> Bool) -> Bool -> Bool"
                    , "poly f x = id f x"
                    , "branch :: Bool -> Bool"
                    , "branch x = if x then False else True"
                    ]
        let program = [G.NonRec owner body | (owner, body) <- G.flattenBinds allCore, G.getOccString owner `elem` ["poly", "branch"]]
            owners = map fst (G.flattenBinds program)
            imports = S.toList (S.fromList (freeVars S.empty program) `S.difference` S.fromList owners)
            cfg = defConfig{LH.typeclass = allow, LH.totalHaskell = True, LH.checkDerived = True}
            spec = giSpec empty
            names = gsName spec
            info =
                empty
                    { giSrc = (giSrc empty){giCbs = program, giDefVars = owners, giImpVars = imports ++ imports}
                    , giSpec = spec{gsConfig = cfg, gsName = names{gsDataConIds = map G.dataConWorkId [G.trueDataCon, G.falseDataCon]}}
                    }
            initialize target = (initCGI cfg info target){CG.freshIndex = seed}
            expected = referencePrefix allow seed info
            actual = preparedPrefix allow seed info
            obligations = ConstraintObligations program (gsMethods $ gsSig $ giSpec info) mempty []
            (expectedCallables, expectedState) = generateConstraints initialize expected [] info obligations
            (actualCallables, actualState) = generateConstraints initialize actual [] info obligations
            (expectedEnv, expectedEnvState) = runState (initEnv expected [] info) (initialize info)
            (actualEnv, actualEnvState) = runState (initEnv actual [] info) (initialize info)
            showTypes = map (\(owner, ty) -> (F.symbol owner, F.showpp ty))
            showEnvironment = map (\(name, ty) -> (name, F.showpp ty)) . toListREnv . CG.renv
        length owners @?= 2
        assertBool "actual imported arrow must consume prefix freshness" (snd actual > seed)
        expectedFInfo <- cgInfoFInfo [] info expectedState
        actualFInfo <- cgInfoFInfo [] info actualState
        actualFInfo @?= expectedFInfo
        CG.freshIndex actualState @?= CG.freshIndex expectedState
        CG.freshIndex actualEnvState @?= CG.freshIndex expectedEnvState
        CG.binds actualState @?= CG.binds expectedState
        CG.binds actualEnvState @?= CG.binds expectedEnvState
        showTypes actualCallables @?= showTypes expectedCallables
        showEnvironment actualEnv @?= showEnvironment expectedEnv
        giQuals info (CG.fEnv actualState) @?= giQuals info (CG.fEnv expectedState)
        CG.cgLits actualState @?= CG.cgLits expectedState
        CG.cgConsts actualState @?= CG.cgConsts expectedState
        CG.cgADTs actualState @?= CG.cgADTs expectedState
        CG.kuts actualState @?= CG.kuts expectedState
        CG.ebinds actualState @?= CG.ebinds expectedState
        CG.termExprs actualState @?= CG.termExprs expectedState
        CG.visitedRefinementOwners actualState @?= CG.visitedRefinementOwners expectedState
        void (evaluate (rnf actualFInfo))

    demandComparison owner bottomSeed poisonedTail observe = do
        let seed = if bottomSeed then error "bottom native prefix seed" else 0
            imports = owner : if poisonedTail then error "bottom native inventory tail" else []
            info = empty{giSrc = (giSrc empty){giImpVars = imports}}
        expected <- try (evaluate (observe (referencePrefix False seed info))) :: IO (Either SomeException Integer)
        actual <- try (evaluate (observe (preparedPrefix False seed info))) :: IO (Either SomeException Integer)
        case (expected, actual) of
            (Right x, Right y) -> (y @?= x) >> pure True
            (Left _, Left _) -> pure False
            _ -> assertBool ("different definedness: " ++ show (expected, actual)) False >> pure False

preparedPrefix :: Bool -> Integer -> TargetInfo -> DefaultTypes
preparedPrefix allow seed info =
    let names = gsName (giSpec info)
     in prepareDefaultTypes
            allow
            seed
            (gsTyconEnv names)
            (gsTcEmbeds names)
            (giImpVars (giSrc info))
            (gsDataConIds names)

-- Project the original three CG actions onto their result and fresh counter.
-- This reference uses CG's existing Freshable instance, not the new pure one.
referencePrefix :: Bool -> Integer -> TargetInfo -> DefaultTypes
referencePrefix allow seed info = (rows, CG.freshIndex final)
  where
    ~(rows, final) = runState original ((initCGI (LH.getConfig info) info info){CG.freshIndex = seed})
    names = gsName (giSpec info)
    imports = giImpVars (giSrc info)
    raw :: [G.Var] -> [(G.Var, SpecType)]
    raw owners = [(owner, addTyConInfo (gsTcEmbeds names) (gsTyconEnv names) (ofType (G.varType owner))) | owner <- owners]
    original :: CG.CG ([(G.Var, SpecType)], [(G.Var, SpecType)], [(G.Var, SpecType)])
    original = do
        a <- mapM (traverse (Fresh.true allow)) (raw imports)
        b <- mapM (traverse (Fresh.true allow)) (raw (gsDataConIds names))
        c <- mapM (traverse (Fresh.true allow)) (raw (filter G.isConLikeId imports))
        pure (a, b, c)
