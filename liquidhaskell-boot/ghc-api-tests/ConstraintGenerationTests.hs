module ConstraintGenerationTests (tests, emptyTarget) where

import Control.DeepSeq (rnf)
import Control.Exception (ErrorCall, displayException, evaluate, try)
import Control.Monad (void)
import Control.Monad.State (evalState, runState)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.List (isInfixOf)
import qualified Data.Store as Store
import qualified DefaultSchemaSharingTests
import GHC.Builtin.Types (mkListTy)
import GHC.Conc (getAllocationCounter)
import GHC.Core.Type (mkVisFunTyMany)
import qualified Language.Fixpoint.SortCheck as SortCheck
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as FC
import Language.Haskell.Liquid.Bare.Check (checkTargetSpec)
import Language.Haskell.Liquid.Bare.Elaborate (alignQueryTelescope)
import Language.Haskell.Liquid.Constraint.Env (lookupREnv)
import Language.Haskell.Liquid.Constraint.Generate (ConstraintObligations (..), generateConstraints)
import Language.Haskell.Liquid.Constraint.Init (initCGI, initEnv)
import Language.Haskell.Liquid.Constraint.Monad (freshPredRef)
import Language.Haskell.Liquid.Constraint.Publication (publicationAdmissible)
import Language.Haskell.Liquid.Constraint.Qualifier (giQuals)
import Language.Haskell.Liquid.Constraint.Split (splitC)
import Language.Haskell.Liquid.Constraint.ToFixpoint (cgInfoFInfo, fixConfig)
import qualified Language.Haskell.Liquid.Constraint.Types as CG
import Language.Haskell.Liquid.GHC.Misc (getSourcePos)
import Language.Haskell.Liquid.Liquid (checkTargetInfo)
import Language.Haskell.Liquid.Types.Errors (Oblig (OCons), TError (..))
import Language.Haskell.Liquid.Types.Names (LHName (..), LHNameSpace (LHLogicName), LHResolvedName (..), LogicName (..), selfSymbol)
import Language.Haskell.Liquid.Types.PredType (replacePreds)
import Language.Haskell.Liquid.Types.RType (PVarBV (..), PredicateBV (..), RPVar, RTVInfo (..), RTVar (..), RTyCon (..), RTypeBV (..), RefB (..), SpecType, TyConInfo (..), UReftBV (..))
import Language.Haskell.Liquid.Types.RTypeOp (rTypeReft, toRSort)
import Language.Haskell.Liquid.Types.RefType (applySolution, ofType, strengthen, toType, uPVar, uTop)
import Language.Haskell.Liquid.Types.Specs
import Language.Haskell.Liquid.Types.Types (AnnInfo (..), CheckedPredicate (..), Cinfo (..), Error, ModName (..), ModType (..), Output (..), QueryTelescope (..), RTAlias (..), TyConMap (..), allErrors)
import Language.Haskell.Liquid.Types.Variance (Variance (..))
import Language.Haskell.Liquid.Types.Visitors (letVars)
import qualified Language.Haskell.Liquid.UX.CmdLine as CmdLine
import qualified Language.Haskell.Liquid.UX.Config as LH
import Language.Haskell.Liquid.UX.Tidy (cinfoError)
import Liquid.GHC.API (mkModuleName)
import qualified Liquid.GHC.API as G
import qualified MethodAdmissionTests
import qualified SplitJudgmentTests
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, testCaseInfo, (@?=))

tests :: (String -> String -> IO G.CoreProgram) -> TestTree
tests compileToCore =
    testGroup
        "constraint generation"
        [ qualifierConfiguration
        , qualifierPreparation
        , initializationSharing compileToCore
        , DefaultSchemaSharingTests.tests emptyTarget compileToCore
        , diagnosticDemand
        , authoredGoalPreservation
        , SplitJudgmentTests.tests emptyTarget
        , publicationSupport
        , solutionInstantiation
        , authoredPresentation compileToCore
        , sourceDependencyIndexing compileToCore
        , bareScopeChecks compileToCore
        , predicateScopeJudgments compileToCore
        , higherKindedPredicateJudgments compileToCore
        , MethodAdmissionTests.tests emptyTarget compileToCore
        , predicateCarrierSubstitution compileToCore
        , concretePredicateArguments compileToCore
        , predicateCarrierPresentation
        , predicateCarrierMetadata
        , freshPredicateGeneration
        , testCase "unsigned callable retains its complete inferred telescope" $ do
            program <-
                compileToCore "UnsignedCallable" $
                    unlines
                        [ "module UnsignedCallable where"
                        , "unsigned :: (a -> a) -> a -> a"
                        , "unsigned f x = f x"
                        ]
            case [(owner, body) | (owner, body) <- G.flattenBinds program, G.getOccString owner == "unsigned"] of
                [(owner, body)] -> do
                    let empty = emptyTarget CmdLine.defConfig{LH.notruetypes = True, LH.checkDerived = True}
                        info = empty{giSrc = (giSrc empty){giCbs = [G.NonRec owner body], giDefVars = [owner]}}
                        obligations = ConstraintObligations (giCbs (giSrc info)) (gsMethods $ gsSig $ giSpec info) mempty []
                        (callables, _) = generateConstraints (initCGI (LH.getConfig info) info) (DefaultSchemaSharingTests.schemas info info) [] info obligations
                    map fst callables @?= [owner]
                    case lookup owner callables of
                        Just inferred -> do
                            let source = ofType (G.varType owner) :: SpecType
                            assertBool "the inferred source telescope changed" (G.eqType (toType False inferred) (toType False source))
                            case inferred of
                                RAllT _ (RFun _ _ (RFun _ _ callbackInput _ _) (RFun _ _ _ _ _) _) _ ->
                                    -- This is an unsolved checking template, not a solver-accepted judgment.
                                    assertBool "the negative-position refinement was erased" (not (F.isTautoReft (rTypeReft callbackInput)))
                                _ -> assertFailure ("missing polymorphic callback telescope: " ++ F.showpp inferred)
                        Nothing -> assertFailure "constraint generation omitted the unsigned source owner"
                _ -> assertFailure "expected one unsigned source definition"
        ]

solutionInstantiation :: TestTree
solutionInstantiation =
    testGroup
        "solved callable instantiation"
        $ [ testCase label $ do
                let occurrence = F.PKVar kvar substitution (F.mkKVarSubst [(formal, F.EVar value)])
                    input = strengthen boolean (uTop (F.Reft (value, occurrence)))
                    expected = predicate resultSort value
                SortCheck.checkSortExpr Nothing F.dummySpan (F.fromListSEnv [(solvedFormal, F.boolSort)]) solved @?= Just F.boolSort
                case applySolution scopes (M.singleton kvar (F.Delayed solved)) [input] of
                    Right [output] -> do
                        rTypeReft output @?= F.Reft (value, expected)
                        SortCheck.checkSortExpr Nothing F.dummySpan (F.fromListSEnv [(value, F.boolSort)]) expected @?= Just F.boolSort
                    other -> assertFailure ("solution application failed: " ++ show other)
          | (label, substitution, resultSort) <-
                [ ("empty type action still instantiates the term", mempty, sourceSort)
                , ("quantified type and term actions are simultaneous", M.fromList [(a, F.FObj b), (b, F.FInt)], F.FObj b)
                ]
          ]
            ++ [ testCase "one source actual supplies both canonical formals" $
                    apply [entry formal solvedFormal, entry formal otherCanonical] (F.PIff (F.EVar solvedFormal) (F.EVar otherCanonical)) [(formal, F.EVar value)]
                        @?= Right [F.Reft (value, F.PIff (F.EVar value) (F.EVar value))]
               , testCase "omitted source actual retains its source identity in every formal" $
                    apply [entry formal solvedFormal, entry formal otherCanonical] (F.PIff (F.EVar solvedFormal) (F.EVar otherCanonical)) []
                        @?= Right [F.Reft (value, F.PIff (F.EVar formal) (F.EVar formal))]
               , testCase "term actuals are simultaneous even when an image names another canonical formal" $
                    apply [entry formal solvedFormal, entry otherSource otherCanonical] (F.PIff (F.EVar solvedFormal) (F.EVar otherCanonical)) [(formal, F.EVar otherCanonical), (otherSource, F.PTrue)]
                        @?= Right [F.Reft (value, F.PIff (F.EVar otherCanonical) F.PTrue)]
               , testCase "spare actual keys cannot rewrite a free solution symbol" $
                    apply [entry formal solvedFormal] (F.PIff (F.EVar solvedFormal) (F.EVar otherSource)) [(formal, F.EVar value), (otherSource, F.PFalse)]
                        @?= Right [F.Reft (value, F.PIff (F.EVar value) (F.EVar otherSource))]
               , testCase "canonical substitution avoids capturing a source actual" $
                    case apply [entry formal solvedFormal] (F.PAll [(x, F.boolSort)] (F.PIff (F.EVar solvedFormal) (F.EVar x))) [(formal, F.EVar x)] of
                        Right [F.Reft (resultValue, F.PAll [(binder, sort)] (F.PIff (F.EVar actual) (F.EVar bound)))] -> do
                            resultValue @?= value
                            sort @?= F.boolSort
                            actual @?= x
                            bound @?= binder
                            assertBool "the actual was captured by the solution binder" (binder /= x)
                        other -> assertFailure ("unexpected capture-avoiding result: " ++ show other)
               , testCase "an explicit empty scope admits a closed solution" $
                    apply [] F.PFalse [] @?= Right [F.Reft (value, F.PFalse)]
               , testCase "a present solution without a scope fails closed" $
                    applyRaw mempty (M.singleton kvar (F.Delayed F.PTrue)) occurrence
                        @?= Left ("solution application: missing result scope for " ++ F.showpp kvar)
               , testCase "scope validation covers every present solution before presentation" $
                    applyRaw mempty (M.singleton kvar (F.Delayed F.PTrue)) F.PTrue
                        @?= Left ("solution application: missing result scope for " ++ F.showpp kvar)
               , testCase "repeated canonical formals cannot silently overwrite an actual" $
                    apply [entry formal solvedFormal, entry otherSource solvedFormal] F.PTrue []
                        @?= Left ("solution application: repeated canonical formal for " ++ F.showpp kvar)
               , testCase "an absent solution retains the historical top policy" $
                    applyRaw mempty mempty occurrence @?= Right [F.Reft (value, F.PTop)]
               ]
  where
    boolean = ofType G.boolTy :: SpecType
    F.Reft (value, _) = rTypeReft boolean
    a = F.symbol ("element" :: String)
    b = F.symbol ("other" :: String)
    formal = F.symbol ("formal" :: String)
    x = F.symbol ("outer" :: String)
    y = F.symbol ("inner" :: String)
    kvar = F.intKvar 0
    solvedFormal = F.symbol ("independently-renamed-formal" :: String)
    otherCanonical = F.symbol ("another-canonical-coordinate" :: String)
    otherSource = F.symbol ("another-source-coordinate" :: String)
    sourceSort = F.FObj a
    solved = predicate sourceSort solvedFormal
    predicate sort parameter =
        F.PAll [(x, sort)] (F.PExist [(y, sort)] (F.PIff (F.EVar parameter) (F.PAnd [F.PAtom F.Eq (F.EVar x) (F.EVar y), F.PAtom F.Eq (F.EVar x) (F.elit (F.dummyLoc (F.symbol ("0" :: String))) sort)])))
    entry source canonical = F.Formal source canonical F.boolSort
    scopes = M.singleton kvar [entry formal solvedFormal]
    occurrence = F.PKVar kvar mempty (F.mkKVarSubst [(formal, F.EVar value)])
    apply formals predicate actuals =
        applyRaw (M.singleton kvar formals) (M.singleton kvar (F.Delayed predicate)) (F.PKVar kvar mempty (F.mkKVarSubst actuals))
    applyRaw resultScopes solution predicate =
        map rTypeReft <$> applySolution resultScopes solution [strengthen boolean (uTop (F.Reft (value, predicate)))]

qualifierPreparation :: TestTree
qualifierPreparation =
    testGroup
        "prepared qualifier extraction"
        [ testCase "signature locals shadow globals without escaping their telescope or constructor" $
            case ofType (mkVisFunTyMany G.boolTy G.boolTy) of
                RFun _ arrowInfo _ _ arrowReft -> do
                    let boolean = ofType G.boolTy :: SpecType
                        F.Reft (value, _) = rTypeReft boolean
                        argument = F.symbol ("argument" :: String)
                        refined expression = strengthen boolean (uTop (F.Reft (value, expression)))
                        local = F.PNot (F.EVar argument)
                        receiver = F.PNot (F.EVar selfSymbol)
                        valuePredicate = F.PNot (F.EVar value)
                        signatures =
                            [ (owner, F.dummyLoc (refined valuePredicate))
                            , (owner, F.dummyLoc (RFun argument arrowInfo (refined local) (refined local) arrowReft))
                            , (owner, F.dummyLoc (refined local))
                            , (owner, F.dummyLoc (refined receiver))
                            ]
                        base = F.fromListSEnv [(value, F.FInt), (argument, F.FInt), (selfSymbol, F.FInt)]
                        empty = qualifierTarget CmdLine.defConfig{LH.eliminate = FC.None}
                        spec = giSpec empty
                        info =
                            empty
                                { giSpec =
                                    spec
                                        { gsSig = (gsSig spec){gsTySigs = signatures}
                                        , gsData = (gsData spec){gsCtors = [(constructor, F.dummyLoc (refined receiver))]}
                                        }
                                }
                        expected variable extra expression =
                            F.mkQ (F.symbol ("Auto" :: String)) ((value, F.boolSort) : extra) expression (getSourcePos variable)
                    giQuals info base
                        @?= [ expected owner [] valuePredicate
                            , expected owner [(argument, F.boolSort)] local
                            , expected constructor [(selfSymbol, F.boolSort)] receiver
                            ]
                _ -> assertFailure "expected a Bool -> Bool qualifier telescope"
        , testCase "alias extraction retains its own selection and exact qualifier order" $ do
            let empty = qualifierTarget CmdLine.defConfig{LH.higherorder = True, LH.eliminate = FC.Some}
                spec = giSpec empty
                body index = integerRefinement (F.PAtom F.Eq (F.EVar integerValue) (F.ECon (F.I index)))
                alias index = F.dummyLoc (RTA (F.dummyLoc (LHNUnresolved LHLogicName (F.symbol ("Alias" ++ show index)))) [] [] (body index))
                info = empty{giSpec = spec{gsQual = (gsQual spec){gsRTAliases = map alias [3, 1, 2]}}}
            giQuals info mempty
                @?= [integerQualifier (F.loc (alias index)) index | index <- [3, 1, 2]]
        , testCaseInfo "base preparation does not multiply environment width by signature count" $ do
            narrowFew <- allocation 8 4
            wideFew <- allocation 256 4
            narrowMany <- allocation 8 64
            wideMany <- allocation 256 64
            assertBool
                ("qualifier base preparation width/count allocation: " ++ show (narrowFew, wideFew, narrowMany, wideMany))
                (wideMany - narrowMany <= 4 * max 0 (wideFew - narrowFew) + 1024 * 1024)
            pure ("allocation bytes (narrow/few, wide/few, narrow/many, wide/many): " ++ show (narrowFew, wideFew, narrowMany, wideMany))
        ]
  where
    owner = G.dataConWorkId G.falseDataCon
    constructor = G.dataConWorkId G.trueDataCon
    integer = ofType G.intTy :: SpecType
    F.Reft (integerValue, _) = rTypeReft integer
    integerRefinement predicate = strengthen integer (uTop (F.Reft (integerValue, predicate)))
    integerQualifier position index =
        F.mkQ
            (F.symbol ("Auto" :: String))
            [(integerValue, F.FInt)]
            (F.PAtom F.Eq (F.EVar integerValue) (F.ECon (F.I index)))
            position
    allocation width count = do
        let unused = foldl' (\result index -> F.FFunc (F.setSort (F.FVar index)) result) F.FInt [0 .. 31]
            base = F.fromListSEnv [(F.symbol ("unused" ++ show index), unused) | index <- [1 :: Int .. width]]
            bodies = [integerRefinement (F.PAtom F.Eq (F.EVar integerValue) (F.ECon (F.I index))) | index <- [1 .. count]]
            empty = qualifierTarget CmdLine.defConfig{LH.eliminate = FC.None, LH.smtsolver = Just FC.Z3}
            spec = giSpec empty
            info = empty{giSpec = spec{gsSig = (gsSig spec){gsTySigs = [(owner, F.dummyLoc body) | body <- bodies]}}}
            qualifiers = giQuals info base
        -- Inputs are outside the thread-local allocation observation; the
        -- public extraction itself, including one base preparation, is not.
        evaluate (rnf (base, bodies))
        before <- getAllocationCounter
        evaluate (rnf qualifiers)
        after <- getAllocationCounter
        qualifiers @?= [integerQualifier (getSourcePos owner) index | index <- [1 .. count]]
        pure (toInteger before - toInteger after)

authoredGoalPreservation :: TestTree
authoredGoalPreservation =
    testGroup
        "authored subtype conclusions"
        [ testCase label $ do
            let direct = conclusions [] predicate
                inherited = conclusions [([F.vv_], predicate)] predicate
            length direct @?= 1
            inherited @?= direct
        | (label, predicate) <-
            [ ("matching ill-sorted equation metadata cannot erase a goal", F.PAtom F.Eq (F.EVar F.vv_) F.PTrue)
            , ("matching well-sorted equation metadata retains the same goal", F.PAtom F.Eq (F.EVar F.vv_) (F.ECon (F.I 0)))
            ]
        ]
  where
    conclusions templates predicate =
        let cfg = CmdLine.defConfig
            empty = emptyTarget cfg
            spec = giSpec empty
            names = gsName spec
            embeds = F.tceInsert G.intTyCon F.intSort F.NoArgs mempty
            info = empty{giSpec = spec{gsData = (gsData spec){gsUnsorted = templates}, gsName = names{gsTcEmbeds = embeds}}}
            integer = ofType G.intTy :: SpecType
            expected = strengthen integer (MkUReft (F.Reft (F.vv_, predicate)) mempty)
         in evalState
                ( do
                    environment <- initEnv (DefaultSchemaSharingTests.schemas info info) [] info
                    map F.crhs <$> splitC False (CG.SubC environment integer expected)
                )
                (initCGI cfg info info)

sourceDependencyIndexing :: (String -> String -> IO G.CoreProgram) -> TestTree
sourceDependencyIndexing compileToCore =
    testGroup
        "source dependency indexing"
        ( [ testCase label $ do
                program <-
                    compileToCore "QueryDependency" $
                        unlines
                            [ "module QueryDependency where"
                            , "helper :: Bool -> Bool"
                            , "helper x = x"
                            , "checked :: Bool -> Bool"
                            , if nested then "checked x = let { {-# NOINLINE nested #-}; nested y = y } in nested x" else "checked x = x"
                            , "query :: Bool -> Bool"
                            , "query x = helper x"
                            ]
                case (named "helper" program, named "checked" program, named "query" program) of
                    ([(helper, helperBody)], [(checked, checkedBody)], [(_, queryBody)]) ->
                        case (identityType checked, identityType helper) of
                            (Just signature, Just helperType) -> do
                                let source = [G.NonRec helper helperBody, G.NonRec checked checkedBody]
                                    info = targetInfo "QueryDependency" source [(checked, signature), (helper, helperType)]
                                    spec = giSpec info
                                    checkOwners = if nested then filter ((== "nested") . G.getOccString) (letVars checkedBody) else [checked]
                                case checkOwners of
                                    [owner] -> do
                                        telescope <- either (\message -> assertFailure message >> fail message) pure (alignQueryTelescope signature queryBody)
                                        let definitions = [(identifier, F.EVar name) | (name, identifier) <- queryValueOwners telescope, not (G.isCoVar identifier)]
                                            meaning = F.eApps (F.EVar (F.symbol helper)) [F.EVar name | (name, _) <- queryValueOwners telescope]
                                            predicate = CheckedPredicate queryBody signature telescope meaning definitions mempty [] []
                                            checks = [RefinementCheck owner queryBody (F.dummyLoc predicate)]
                                        assertSafe info{giSpec = spec{gsSig = (gsSig spec){gsReftChecks = checks}}}
                                    _ -> assertFailure ("expected the exact lexical declaration owner: " ++ show (map G.getOccString (letVars checkedBody)))
                            _ -> assertFailure "expected Boolean source arrows"
                    _ -> assertFailure "expected the actual query and source owners"
          | (label, nested) <- [("a query-only Core dependency precedes its declaration owner", False), ("a nested declaration's query-only dependency retains its enclosing group", True)]
          ]
            ++ [ testCase "recursive Core edges retain their checked metric scope" $ do
                    program <-
                        compileToCore "MetricDependency" $
                            unlines
                                [ "module MetricDependency where"
                                , "loop :: Bool -> Bool"
                                , "loop True = other False"
                                , "loop False = False"
                                , "other :: Bool -> Bool"
                                , "other True = loop False"
                                , "other False = False"
                                ]
                    case (named "loop" program, named "other" program) of
                        ([loop@(loopOwner, _)], [other@(otherOwner, _)]) ->
                            case (plainType loopOwner, plainType otherOwner) of
                                (Just loopType, Just otherType) -> do
                                    let signatures = [(loopOwner, loopType), (otherOwner, otherType)]
                                        info = targetInfo "MetricDependency" [G.Rec [other, loop]] signatures
                                        spec = giSpec info
                                        metric = F.EIte (F.EVar (F.symbol ("input" :: String))) (F.ECon (F.I 1)) (F.ECon (F.I 0))
                                        names = (gsName spec){gsTcEmbeds = F.tceFromList [(G.boolTyCon, (F.boolSort, F.NoArgs))]}
                                        literals = [(F.symbol (G.dataConWorkId constructor), F.boolSort) | constructor <- [G.trueDataCon, G.falseDataCon]]
                                        constructors = [(G.dataConWorkId constructor, F.dummyLoc (strengthen (ofType G.boolTy) (uTop (F.exprReft (truth :: F.Expr))))) | (constructor, truth) <- [(G.trueDataCon, F.PTrue), (G.falseDataCon, F.PFalse)]]
                                    assertSafe info{giSpec = spec{gsSig = (gsSig spec){gsTexprs = [(owner, F.dummyLoc ty, [F.dummyLoc metric]) | (owner, ty) <- signatures]}, gsName = names, gsImps = literals, gsData = (gsData spec){gsCtors = constructors}}}
                                _ -> assertFailure "expected Boolean recursive arrows"
                        _ -> assertFailure "expected both actual recursive owners"
               ]
        )
  where
    named name program = [(owner, body) | (owner, body) <- G.flattenBinds program, G.getOccString owner == name]
    identityType owner = case ofType (G.varType owner) of
        RFun _ info input output refinement ->
            let argument = F.symbol ("input" :: String)
             in Just $ RFun argument info input (strengthen output (uTop (F.exprReft (F.EVar argument :: F.Expr)))) refinement
        _ -> Nothing
    plainType owner = case ofType (G.varType owner) of
        RFun _ info input output refinement -> Just $ RFun (F.symbol ("input" :: String)) info input output refinement
        _ -> Nothing
    targetInfo name source signatures =
        let empty = emptyTarget CmdLine.defConfig{LH.checkDerived = True, LH.checkRefinements = True, LH.totalHaskell = True, LH.noannotations = True, LH.smtsolver = Just FC.Z3}
            spec = giSpec empty
         in empty
                { giSrc = (giSrc empty){giTarget = name ++ ".hs", giTargetMod = ModName Target (mkModuleName name), giCbs = source, giDefVars = concatMap G.bindersOf source}
                , giSpec = spec{gsSig = (gsSig spec){gsTySigs = [(owner, F.dummyLoc ty) | (owner, ty) <- signatures]}}
                }
    assertSafe info = do
        (output, _, publication) <- checkTargetInfo info
        case (o_result output, publication) of
            (F.Safe _, Just (F.Safe _)) -> pure ()
            other -> assertFailure ("source dependency judgment was not established: " ++ show other)

initializationSharing :: (String -> String -> IO G.CoreProgram) -> TestTree
initializationSharing compileToCore =
    testGroup
        "query initialization sharing"
        [ testCase "prepared initialization retains stage owners, templates and target" $ do
            let initialize = initCGI cfg base
            mapM_ (checkStage initialize) [stage False, stage True]
        , testCase "unselected base obligations and templates are not demanded" $ do
            let spec = giSpec base
                poisoned =
                    base
                        { giSpec =
                            spec
                                { gsSig = (gsSig spec){gsReftChecks = [error "unselected base owner"]}
                                , gsData = (gsData spec){gsUnsorted = [([], error "unselected base template")]}
                                }
                        }
            checkStage (initCGI cfg poisoned) (stage True)
        , testCase "preparing an initializer does not demand its source or configuration" $
            void (evaluate (initCGI (error "unused configuration") (error "unused source")))
        , testCase "authored and filtered Core views retain separate literal inventories" $ do
            program <- compileToCore "SeedLiterals" "module SeedLiterals where\nliteral = \"seed-literal\"\n"
            let authored = base{giSrc = (giSrc base){giCbs = program}}
                authoredState = initCGI cfg authored authored
                sourceState = initCGI cfg base base
            assertBool "Core literal inventory was accidentally shared between views" (CG.cgLits authoredState /= CG.cgLits sourceState)
        ]
  where
    cfg = CmdLine.defConfig
    owner = G.dataConWorkId G.falseDataCon
    other = G.dataConWorkId G.trueDataCon
    boolean = ofType G.boolTy :: SpecType
    name = F.symbol ("seed-literal-sort" :: String)
    template = F.PAtom F.Eq (F.EVar name) F.PTrue
    base =
        let empty = emptyTarget cfg
            spec = giSpec empty
         in empty{giSpec = spec{gsData = (gsData spec){gsMeas = [(name, F.dummyLoc boolean)]}}}
    stage valid =
        let spec = giSpec base
            selected = if valid then other else owner
            predicate = CheckedPredicate (G.Var selected) boolean (QueryTelescope [] []) (if valid then F.PTrue else F.PFalse) [] mempty [] []
            check = RefinementCheck selected (G.Var selected) (F.dummyLoc predicate)
         in base
                { giSrc = (giSrc base){giTarget = if valid then "checking" else "admission"}
                , giSpec =
                    spec
                        { gsSig = (gsSig spec){gsReftChecks = [check], gsTySigs = [(selected, F.dummyLoc boolean)]}
                        , gsData = (gsData spec){gsUnsorted = if valid then [([], template)] else []}
                        }
                }
    checkStage initialize info = do
        let shared = initialize info
            direct = initCGI cfg info info
            ownerKeys = M.keysSet . CG.refinementChecksByOwner
        ownerKeys shared @?= ownerKeys direct
        F.isEmptyTemplates (CG.unsorted shared) @?= F.isEmptyTemplates (CG.unsorted direct)
        F.matchesTemplates (CG.unsorted shared) template @?= F.matchesTemplates (CG.unsorted direct) template
        giTarget (giSrc (CG.ghcI shared)) @?= giTarget (giSrc info)
        CG.cgLits shared @?= CG.cgLits direct
        CG.cgConsts shared @?= CG.cgConsts direct
        CG.cgADTs shared @?= CG.cgADTs direct
        CG.freshIndex shared @?= 0
        F.bindEnvSize (CG.binds shared) @?= 0
        S.null (CG.visitedRefinementOwners shared) @?= True

qualifierTarget :: LH.Config -> TargetInfo
qualifierTarget cfg =
    let empty = emptyTarget cfg
        spec = giSpec empty
        names = gsName spec
        embeds = F.tceInsert G.intTyCon F.FInt F.NoArgs (F.tceInsert G.boolTyCon F.boolSort F.NoArgs mempty)
     in empty{giSpec = spec{gsName = names{gsTcEmbeds = embeds}}}

publicationSupport :: TestTree
publicationSupport =
    testGroup
        "publication support"
        [ testCase (label ++ " " ++ position ++ " " ++ ownership) $
            publicationAdmissible (S.singleton owner) (place payload) (F.Unsafe mempty failures)
                @?= (eligible && absent)
        | (label, absent, payload) <-
            [ ("empty", True, emptyLiftedSpec)
            , ("unrelated", True, named (LHNResolved (LHRGHC otherName) unrelated))
            , ("canonical identity", False, named (LHNResolved (LHRLogic (LogicName (F.symbol (G.getOccString ownerName)) (G.nameModule ownerName) Nothing)) unrelated))
            , ("parser spelling", False, named (LHNResolved (LHRGHC otherName) failedSymbol))
            , ("reflected identity", False, named (LHNResolved (LHRLogic (LogicName unrelated (G.nameModule ownerName) (Just ownerName))) unrelated))
            , ("generated identity", False, named (LHNResolved (LHRLogic (GeneratedLogicName failedSymbol)) unrelated))
            , ("unresolved", False, named (LHNUnresolved LHLogicName unrelated))
            , ("serialized index", False, named (LHNResolved (LHRIndex 0) unrelated))
            , ("raw symbol", False, emptyLiftedSpec{liftedPrivateReflects = S.singleton (F.dummyLoc failedSymbol)})
            ]
        , (position, place) <- [("target", (: [])), ("dependency", \spec -> [emptyLiftedSpec, spec])]
        , (ownership, eligible, failures) <-
            [ ("private", True, [Just owner])
            , ("duplicate", True, [Just owner, Just owner])
            , ("unowned", False, [Nothing])
            , ("mixed", False, [Just owner, Nothing])
            , ("ineligible", False, [Just other])
            , ("empty", False, [])
            ]
        ]
  where
    owner = G.dataConWorkId G.trueDataCon
    other = G.dataConWorkId G.falseDataCon
    ownerName = G.getName owner
    otherName = G.getName other
    failedSymbol = F.symbol owner
    unrelated = F.symbol ("unrelated" :: String)
    named name = emptyLiftedSpec{liftedUsedDataCons = S.singleton name}

diagnosticDemand :: TestTree
diagnosticDemand =
    testCase "forcing constraint metadata defers its diagnostic, but extraction and equality do not" $ do
        let failure = "constraint diagnostic payload demanded"
            owner = Just (G.dataConWorkId G.trueDataCon)
            deferred = Ci G.noSrcSpan (Just (F.Delayed (error failure))) owner
            actualType = ofType G.boolTy :: SpecType
            expectedType = ofType G.intTy :: SpecType
            context = M.singleton (F.symbol ("local" :: String)) actualType
            expected = ErrSubType G.noSrcSpan mempty (Just 17) context actualType expectedType
            concrete = Ci G.noSrcSpan (Just (F.Delayed expected)) owner
        evaluate (rnf deferred)
        extracted <- try (evaluate (cinfoError deferred)) :: IO (Either ErrorCall Error)
        compared <- try (evaluate (deferred == concrete)) :: IO (Either ErrorCall Bool)
        case extracted of
            Left exception -> assertBool "extraction failed for an unrelated reason" (failure `isInfixOf` displayException exception)
            Right _ -> assertFailure "extracting the diagnostic did not demand it"
        case compared of
            Left exception -> assertBool "equality failed for an unrelated reason" (failure `isInfixOf` displayException exception)
            Right _ -> assertFailure "metadata equality ignored its diagnostic"
        case cinfoError concrete of
            ErrSubType location message identifier bindings actual wanted -> do
                location @?= G.noSrcSpan
                message @?= mempty
                identifier @?= Just 17
                bindings @?= context
                actual @?= actualType
                wanted @?= expectedType
            _ -> assertFailure "extracting the diagnostic changed its error constructor"
        F.srcSpan concrete @?= F.srcSpan deferred
        ci_var concrete @?= owner

bareScopeChecks :: (String -> String -> IO G.CoreProgram) -> TestTree
bareScopeChecks compileToCore =
    testCase "prepared bare checks preserve global, Core, and telescope scopes" $ do
        program <-
            compileToCore "PreparedBareScopes" $
                unlines
                    [ "module PreparedBareScopes where"
                    , "checked :: Bool -> Bool"
                    , "checked outer = local outer"
                    , "  where"
                    , "    {-# NOINLINE local #-}"
                    , "    local :: Bool -> Bool"
                    , "    local inner = outer && inner"
                    ]
        let named name = [v | v <- letVars program, G.getOccString v == name]
        case (named "checked", named "outer", named "local") of
            ([owner], [outer], [local]) ->
                case ofType (G.varType owner) of
                    original@(RFun _ info domain result refinement) -> do
                        let empty = emptyTarget CmdLine.defConfig
                            spec = giSpec empty
                            names = gsName spec
                            embedded = F.tceInsert G.boolTyCon F.boolSort F.NoArgs mempty
                            scopeSpec = spec{gsName = names{gsTcEmbeds = embedded}}
                            source = (giSrc empty){giCbs = program, giDefVars = [owner]}
                            sorted sort = F.RR sort (F.Reft (F.symbol ("vv" :: String), F.PTrue))
                            global symbol sort = F.fromListSEnv [(symbol, sorted sort)]
                            check environment variable ty metrics =
                                let located = F.dummyLoc ty
                                    signatures =
                                        (gsSig scopeSpec)
                                            { gsTySigs = [(variable, located)]
                                            , gsTexprs = [(variable, located, F.dummyLoc <$> metrics)]
                                            }
                                 in checkTargetSpec [] [] [mempty] source environment program scopeSpec{gsSig = signatures}
                            accepted label outcome = case outcome of
                                Right () -> pure ()
                                Left diagnostics -> assertFailure (label ++ ": " ++ F.showpp (allErrors diagnostics))
                            rejected label expected outcome = case outcome of
                                Left diagnostics ->
                                    assertBool
                                        (label ++ ": " ++ F.showpp (allErrors diagnostics))
                                        (not (null (allErrors diagnostics)) && all expected (allErrors diagnostics))
                                Right () -> assertFailure (label ++ ": unexpectedly accepted")
                            typeError ErrTySpec{} = True
                            typeError _ = False
                            termError ErrTermSpec{} = True
                            termError _ = False
                            predicate symbol = uTop (F.exprReft (F.EVar symbol :: F.Expr))
                            arrow symbol input output = RFun symbol info input output refinement
                            outerSymbol = F.symbol outer
                            argument = F.symbol ("refinedArgument" :: String)
                            metric = F.symbol ("globalMetric" :: String)
                            second = F.symbol ("secondObligation" :: String)
                            obligation entries body = RRTy entries refinement OCons body
                            captured = arrow argument domain (strengthen result (predicate outerSymbol))
                            contraryOuter = global outerSymbol F.FInt
                            contraryArgument = global argument F.FInt
                        -- Termination metrics need globals even when the Core delta is empty.
                        accepted "global termination metric" (check (global metric F.FInt) owner original [F.EVar metric])
                        rejected "missing termination metric" termError (check mempty owner original [F.EVar metric])
                        rejected "non-numeric termination metric" termError (check (global metric F.boolSort) owner original [F.EVar metric])
                        -- The actual Core lambda shadows a contrary global only for its local signature.
                        accepted "Core local shadows global" (check contraryOuter local captured [])
                        rejected "Core local does not escape" typeError (check contraryOuter owner captured [])
                        accepted "local termination retains globals" (check (global metric F.FInt) local original [F.EVar metric])
                        -- A function argument scopes over its result, not over its own domain.
                        accepted "function result scope" (check contraryArgument owner (arrow argument domain (strengthen result (predicate argument))) [])
                        rejected "function own-domain scope" typeError (check contraryArgument owner (arrow argument (strengthen domain (predicate argument)) result) [])
                        let p = PV (F.symbol ("p#1#1" :: String)) (toRSort domain) []
                            q = p{pname = F.symbol ("p#1#40" :: String)}
                            abstract :: SpecType -> RPVar -> SpecType
                            abstract ty pv = strengthen ty (MkUReft mempty (Pr [uPVar pv]))
                            nested pv = arrow argument domain (RAllP pv (abstract result pv))
                        accepted "predicate binder scopes over a nested result" (check mempty owner (nested p) [])
                        accepted
                            "outer predicate remains in a nested predicate body"
                            (check mempty owner (RAllP p (arrow argument domain (RAllP q (abstract result p)))) [])
                        accepted
                            "distinct predicate binders retain their lexical scopes"
                            (check mempty owner (RAllP p (arrow argument (abstract domain p) (RAllP q (abstract result q)))) [])
                        -- Raw internal types need lexical lookup even without parser hygiene.
                        let shadowed = p{ptype = toRSort (ofType G.intTy :: SpecType)}
                        accepted
                            "nearest raw predicate binder shadows its outer sort"
                            (check mempty owner (RAllP shadowed (nested p)) [])
                        rejected
                            "predicate domain binder does not escape to result"
                            typeError
                            (check mempty owner (arrow argument (RAllP p (abstract domain p)) (abstract result p)) [])
                        rejected
                            "predicate result binder does not escape to domain"
                            typeError
                            (check mempty owner (arrow argument (abstract domain p) (RAllP p (abstract result p))) [])
                        -- Obligation entries form a sequential telescope, separate from its body.
                        let entries = [(argument, domain), (second, strengthen domain (predicate argument))]
                        accepted "sequential obligation entries" (check contraryArgument owner (obligation entries original) [])
                        rejected "obligation later entry is not in scope" typeError (check contraryArgument owner (obligation (reverse entries) original) [])
                        rejected "obligation entries do not escape" typeError (check contraryArgument owner (obligation entries (arrow second domain (strengthen result (predicate argument)))) [])
                    _ -> assertFailure "expected the Bool -> Bool checking telescope"
            _ -> assertFailure "expected the source owner, its lambda, and its local function"

predicateScopeJudgments :: (String -> String -> IO G.CoreProgram) -> TestTree
predicateScopeJudgments compileToCore =
    testGroup
        "nested predicate source judgments"
        [ testCase label $ do
            program <- compileToCore moduleName (unlines ["module " ++ moduleName ++ " where", "checked :: Bool -> Bool -> Bool", "checked outer inner = " ++ selected])
            case [(owner, body) | (owner, body) <- G.flattenBinds program, G.getOccString owner == "checked"] of
                [(owner, body)] ->
                    case ofType (G.varType owner) of
                        RFun _ outerInfo domain (RFun _ innerInfo input result innerReft) outerReft -> do
                            let p = PV (F.symbol ("p#1#1" :: String)) (toRSort domain) []
                                q = if shadow then p else p{pname = F.symbol ("p#1#40" :: String)}
                                abstract :: SpecType -> RPVar -> SpecType
                                abstract ty pv = strengthen ty (MkUReft mempty (Pr [uPVar pv]))
                                declared = RAllP p (RFun (F.symbol ("outer" :: String)) outerInfo (abstract domain p) (RAllP q (RFun (F.symbol ("inner" :: String)) innerInfo (abstract input q) (abstract result q) innerReft)) outerReft)
                                empty = emptyTarget CmdLine.defConfig{LH.checkDerived = True, LH.checkRefinements = True, LH.totalHaskell = True, LH.noannotations = True, LH.smtsolver = Just FC.Z3}
                                source = (giSrc empty){giTarget = moduleName ++ ".hs", giTargetMod = ModName Target (mkModuleName moduleName), giCbs = [G.NonRec owner body], giDefVars = [owner]}
                                spec = giSpec empty
                                info = empty{giSrc = source, giSpec = spec{gsSig = (gsSig spec){gsTySigs = [(owner, F.dummyLoc declared)]}}}
                            (output, _, _) <- checkTargetInfo info
                            case (accepts, o_result output) of
                                (True, F.Safe _) -> pure ()
                                (False, F.Unsafe _ _) -> pure ()
                                _ -> assertFailure (label ++ ": " ++ show (o_result output))
                        _ -> assertFailure "expected a Bool -> Bool -> Bool source telescope"
                _ -> assertFailure "expected one checked source owner"
        | (label, moduleName, selected, accepts, shadow) <-
            [ ("a nested universally quantified callback returns its own input", "NestedPredicateIdentity", "inner", True, False)
            , ("an outer predicate cannot establish an independent inner result", "NestedPredicateCapture", "outer", False, False)
            , ("raw same-name nested predicates retain the inner identity", "RawNestedPredicateIdentity", "inner", True, True)
            , ("raw same-name nested predicates cannot capture an outer input", "RawNestedPredicateCapture", "outer", False, True)
            ]
        ]

concretePredicateArguments :: (String -> String -> IO G.CoreProgram) -> TestTree
concretePredicateArguments compileToCore = testCase "concrete predicate arguments use one simultaneous substitution" $ do
    program <- compileToCore "ConcretePredicateArguments" "module ConcretePredicateArguments where\nidentity :: a -> a\nidentity x = x\n"
    case [ofType (G.varType owner) | (owner, _) <- G.flattenBinds program, G.getOccString owner == "identity"] of
        [RAllT _ (RFun _ _ carrier@RVar{} _ _) _] -> do
            let symbol = F.symbol :: String -> F.Symbol
                declared = [symbol "first", symbol "second"]
                fresh = [symbol "freshFirst", symbol "freshSecond"]
                boolean = toRSort (ofType G.boolTy :: SpecType)
                p = PV (symbol "concretePredicate") (toRSort carrier) [(boolean, name, F.EVar name) | name <- declared]
                use actuals = (uPVar p){pargs = [(mempty, name, actual) | (name, actual) <- zip declared actuals]}
                apply formals actuals =
                    let input = strengthen carrier (MkUReft mempty (Pr [use actuals]))
                        range = strengthen carrier (uTop (F.Reft (symbol "VV", F.pAnd (F.EVar <$> formals))))
                     in replacePreds "concrete argument control" input [(p, RProp [(name, boolean) | name <- formals] range)]
                checks =
                    [ ("identity", declared, F.EVar <$> declared, F.EVar <$> declared)
                    , ("fresh replacement formals", fresh, F.EVar <$> declared, F.EVar <$> declared)
                    , ("mixed actuals", fresh, [F.EVar (symbol "first"), F.EVar (symbol "other")], [F.EVar (symbol "first"), F.EVar (symbol "other")])
                    , ("expression actuals", fresh, [F.PTrue, F.PFalse], [F.PTrue, F.PFalse])
                    , ("all defaults", fresh, [], F.EVar <$> declared)
                    , ("suffix default", fresh, [F.EVar (symbol "other")], [F.EVar (symbol "other"), F.EVar (symbol "second")])
                    ]
            mapM_
                ( \(label, formals, actuals, expected) -> case apply formals actuals of
                    RVar kept root -> do
                        assertBool (label ++ ": carrier changed") (G.eqType (toType False (RVar kept mempty :: SpecType)) (toType False carrier))
                        ur_pred root @?= Pr []
                        F.reftPred (ur_reft root) @?= F.pAnd expected
                    _ -> assertFailure (label ++ ": substitution changed the carrier representation")
                )
                checks
        _ -> assertFailure "expected a polymorphic variable carrier"

predicateCarrierPresentation :: TestTree
predicateCarrierPresentation = testCase "predicate substitution refuses unsupported equal-carrier presentations" $
    case ofType (mkListTy G.boolTy) :: SpecType of
        canonical@(RApp c [argument] [] _) -> do
            let applied = RAppTy (RApp c [] [] mempty) argument mempty
                p = PV (F.symbol ("presentationPredicate" :: String)) (toRSort canonical) []
                input = strengthen applied (MkUReft mempty (Pr [uPVar p]))
                replacement = strengthen canonical (uTop (F.Reft (F.symbol ("vv" :: String), F.PFalse)))
                substituted = replacePreds "presentation control" input [(p, RProp [] replacement)]
            assertBool "the presentations must have equal GHC carriers" (G.eqType (toType False applied) (toType False canonical))
            case replacePreds "atomic presentation control" input [(p, RProp [] (RHole (uTop (F.Reft (F.symbol ("vv" :: String), F.PFalse)))))] of
                RAppTy keptHead keptArgument root -> do
                    keptHead @?= RApp c [] [] mempty
                    keptArgument @?= argument
                    ur_pred root @?= Pr []
                    F.reftPred (ur_reft root) @?= F.PFalse
                _ -> assertFailure "atomic substitution changed the application presentation"
            outcome <- try (evaluate (rnf substituted)) :: IO (Either ErrorCall ())
            case outcome of
                Left diagnostic -> assertBool "must explain the unsupported carrier" ("carrier" `isInfixOf` displayException diagnostic)
                Right () -> assertFailure ("unsupported carrier was silently admitted: " ++ F.showpp substituted)
        _ -> assertFailure "expected a canonical list carrier"

predicateCarrierMetadata :: TestTree
predicateCarrierMetadata = testCase "atomic predicate instantiation preserves owned metadata and dependent formals" $
    case ofType (mkListTy G.boolTy) :: SpecType of
        canonical@(RApp c [argument] [] r) -> do
            let formal = F.symbol ("declaredFormal" :: String)
                freshFormal = F.symbol ("freshFormal" :: String)
                actual = F.symbol ("actualArgument" :: String)
                sort = toRSort argument
                p = PV (F.symbol ("atomicPredicate" :: String)) (toRSort canonical) [(sort, formal, F.EVar formal)]
                ownedInfo = TyConInfo [Contravariant] [Invariant] Nothing
                owned = RTyCon (rtc_tc c) [p] ownedInfo
                child = strengthen argument (uTop (F.Reft (F.symbol ("child" :: String), F.PFalse)))
                property = RProp [(formal, sort)] child
                carrier = RApp owned [child] [property] r
                root = uTop (F.Reft (F.symbol ("atomicValue" :: String), F.EVar freshFormal))
                apply used = replacePreds "atomic metadata control" (strengthen carrier (MkUReft mempty (Pr [used]))) [(p, RProp [(freshFormal, sort)] (RHole root))]
                check used expected = case apply used of
                    RApp (RTyCon _ retainedPredicates retainedInfo) [keptChild] [keptProperty] instantiated -> do
                        show retainedPredicates @?= show [p]
                        show retainedInfo @?= show ownedInfo
                        keptChild @?= child
                        keptProperty @?= property
                        ur_pred instantiated @?= Pr []
                        F.reftPred (ur_reft instantiated) @?= F.EVar expected
                    _ -> assertFailure "atomic substitution changed the owned carrier"
            check (uPVar p) formal
            check (uPVar p){pargs = [(mempty, formal, F.EVar actual)]} actual
            check (uPVar p){pargs = []} formal
            let rejects label replacement used = do
                    outcome <- try (evaluate (rnf (replacePreds label (strengthen carrier (MkUReft mempty (Pr [used]))) [(p, replacement)]))) :: IO (Either ErrorCall ())
                    case outcome of
                        Left diagnostic -> assertBool label ("carrier" `isInfixOf` displayException diagnostic || "arity" `isInfixOf` displayException diagnostic)
                        Right () -> assertFailure (label ++ ": malformed atomic instantiation admitted")
            rejects "formal arity" (RProp [] (RHole root)) (uPVar p)
            rejects "formal carrier" (RProp [(freshFormal, toRSort (ofType G.intTy :: SpecType))] (RHole root)) (uPVar p)
            rejects "actual arity" (RProp [(freshFormal, sort)] (RHole root)) (uPVar p){pargs = [(mempty, formal, F.EVar actual), (mempty, actual, F.EVar actual)]}
        _ -> assertFailure "expected a canonical list carrier"

freshPredicateGeneration :: TestTree
freshPredicateGeneration = testCase "fresh predicate inference uses one scoped root KVar and fresh dependent formals" $ do
    let info = emptyTarget CmdLine.defConfig
        carrier = ofType (mkListTy G.boolTy) :: SpecType
        boolean = ofType G.boolTy :: SpecType
        formal = F.symbol ("sourceFormal" :: String)
        p = PV (F.symbol ("freshPredicate" :: String)) (toRSort carrier) [(toRSort boolean, formal, F.EVar formal)]
        action = do
            environment <- initEnv (DefaultSchemaSharingTests.schemas info info) [] info
            freshPredRef environment p
        (property, state) = runState action (initCGI (LH.getConfig info) info info)
    case property of
        RProp [(freshFormal, _)] (RHole root) -> do
            assertBool "the dependent formal must be fresh" (freshFormal /= formal)
            case CG.hsWfs state of
                [CG.WfC environment (RApp _ [child] [] checkedRoot)] -> do
                    checkedRoot @?= root
                    assertBool "child contracts must not be inferred for a Boolean predicate" (F.isTautoReft (rTypeReft child))
                    case lookupREnv freshFormal (CG.renv environment) of
                        Just binding -> do
                            assertBool "fresh formal has its declared carrier" (G.eqType (toType False binding) G.boolTy)
                            assertBool "fresh formal must have a trivial checking type" (F.isTautoReft (rTypeReft binding))
                        Nothing -> assertFailure "fresh formal escaped its wellformedness scope"
                _ -> assertFailure "missing root-only predicate wellformedness constraint"
            assertBool "predicate KVar profiling must be retained" ("PredInstE" `isInfixOf` F.showpp (CG.kvProf state))
            case F.reftPred (ur_reft root) of
                F.PKVar kvar _ _ -> do
                    let instantiated = replacePreds "fresh formal control" (strengthen carrier (MkUReft mempty (Pr [uPVar p]))) [(p, property)]
                    case M.lookup kvar (F.exprKVars (F.reftPred (rTypeReft instantiated))) of
                        Just [substitution] -> M.lookup freshFormal (F.fromKVarSubst substitution) @?= Just (F.EVar formal)
                        _ -> assertFailure "the root KVar changed or was duplicated"
                _ -> assertFailure "fresh predicate is not one atomic root KVar"
        _ -> assertFailure "fresh predicate inference produced a structural contract"

predicateCarrierSubstitution :: (String -> String -> IO G.CoreProgram) -> TestTree
predicateCarrierSubstitution compileToCore = testCase "predicate instantiation preserves compound carriers and obligation roots" $ do
    program <- compileToCore "PredicateCarrierSubstitution" "module PredicateCarrierSubstitution where\npoly :: f Bool -> f Bool\npoly x = x\n"
    case [ofType (G.varType owner) | (owner, _) <- G.flattenBinds program, G.getOccString owner == "poly"] of
        [original@(RAllT variable body@(RFun _ _ carrier _ _) outerRef)] -> do
            let abstract :: SpecType -> RPVar -> SpecType
                abstract ty pv = strengthen ty (MkUReft mempty (Pr [uPVar pv]))
                falseRef :: UReftBV F.Symbol F.Symbol
                falseRef = uTop (F.Reft (F.symbol ("vv" :: String), F.PFalse))
                instantiate :: SpecType -> SpecType -> SpecType
                instantiate target replacement =
                    let p = PV (F.symbol ("carrierPredicate" :: String)) (toRSort replacement) []
                     in replacePreds "carrier substitution control" (abstract target p) [(p, RProp [] (RHole falseRef))]
                checkRoot :: String -> SpecType -> IO ()
                checkRoot label instantiated = do
                    let root = case instantiated of
                            RAppTy _ _ r -> r
                            RAllT _ _ r -> r
                            _ -> mempty
                    ur_pred root @?= Pr []
                    assertBool (label ++ ": replacement refinement disappeared") (F.reftPred (ur_reft root) == F.PFalse)
                boolType = ofType G.boolTy :: SpecType
            let metadata = ty_var_info variable
                changed = RAllT variable{ty_var_info = metadata{rtv_is_pol = not (rtv_is_pol metadata)}} body outerRef
            case instantiate changed changed of
                RAllT retained keptBody _ -> do
                    ty_var_info retained @?= metadata{rtv_is_pol = not (rtv_is_pol metadata)}
                    keptBody @?= body
                _ -> assertFailure "atomic substitution changed the quantified carrier"
            checkRoot "higher-kinded application" (instantiate carrier carrier)
            checkRoot "type-quantified carrier" (instantiate original original)
            let p = PV (F.symbol ("obligationPredicate" :: String)) (toRSort boolType) []
                obligation = RRTy [] (MkUReft mempty (Pr [uPVar p])) OCons boolType
                instantiated = replacePreds "obligation substitution control" obligation [(p, RProp [] (RHole falseRef))]
            case instantiated of
                RRTy [] root OCons _ -> do
                    ur_pred root @?= Pr []
                    F.reftPred (ur_reft root) @?= F.PFalse
                _ -> assertFailure "obligation structure changed"
        _ -> assertFailure "expected a higher-kinded carrier under a type quantifier"

higherKindedPredicateJudgments :: (String -> String -> IO G.CoreProgram) -> TestTree
higherKindedPredicateJudgments compileToCore =
    testGroup
        "higher-kinded predicate source judgments"
        [ testCase label $ do
            program <- compileToCore moduleName (unlines ["module " ++ moduleName ++ " where", "checked :: (f Bool -> Bool) -> f Bool -> Bool", "checked selector container = selector container"])
            case [(owner, body) | (owner, body) <- G.flattenBinds program, G.getOccString owner == "checked"] of
                [(owner, body)] -> case ofType (G.varType owner) of
                    RAllT tv (RFun x i (RFun y j carrier result cr) (RFun z k _ _ ar) rr) tr -> do
                        let p = PV (F.symbol ("p#1#1" :: String)) (toRSort result) []
                            q = p{pname = F.symbol ("q#1#1" :: String)}
                            abstract :: SpecType -> RPVar -> SpecType
                            abstract ty pv = strengthen ty (MkUReft mempty (Pr [uPVar pv]))
                            member pv = case carrier of
                                RAppTy headType argument r -> RAppTy headType (abstract argument pv) r
                                _ -> carrier
                            callback = RAllP p (RFun y j (member p) (abstract result p) cr)
                            outcome = if accepts then abstract result q else strengthen result (uTop (F.Reft (F.symbol ("vv" :: String), F.PFalse)))
                            input = if accepts then member q else carrier
                            arrow = RFun x i callback (RFun z k input outcome ar) rr
                            declared = RAllT tv (if accepts then RAllP q arrow else arrow) tr
                            empty = emptyTarget CmdLine.defConfig{LH.checkDerived = True, LH.checkRefinements = True, LH.totalHaskell = True, LH.noannotations = True, LH.smtsolver = Just FC.Z3}
                            source = (giSrc empty){giTarget = moduleName ++ ".hs", giTargetMod = ModName Target (mkModuleName moduleName), giCbs = [G.NonRec owner body], giDefVars = [owner]}
                            spec = giSpec empty
                            info = empty{giSrc = source, giSpec = spec{gsSig = (gsSig spec){gsTySigs = [(owner, F.dummyLoc declared)]}}}
                        assertBool "control requires an RAppTy carrier" (case carrier of RAppTy{} -> True; _ -> False)
                        (output, _, _) <- checkTargetInfo info
                        case (accepts, o_result output) of
                            (True, F.Safe _) -> pure ()
                            (False, F.Unsafe _ _) -> pure ()
                            _ -> assertFailure (label ++ ": " ++ show (o_result output))
                    _ -> assertFailure "expected a higher-kinded callback source telescope"
                _ -> assertFailure "expected one checked source owner"
        | (label, moduleName, accepts) <- [("preserves the member predicate", "HigherKindedPredicateIdentity", True), ("cannot produce a false result from an unrefined container", "HigherKindedPredicateCapture", False)]
        ]

authoredPresentation :: (String -> String -> IO G.CoreProgram) -> TestTree
authoredPresentation compileToCore =
    testCase "source presentation contains the authored judgment, not its admission template" $ do
        program <-
            compileToCore "AuthoredPresentation" $
                unlines
                    [ "module AuthoredPresentation where"
                    , "{-# NOINLINE helper #-}"
                    , "helper :: a -> a"
                    , "helper x = x"
                    , "checked :: Bool -> Bool"
                    , "checked x = helper x"
                    ]
        let named name = [(owner, body) | (owner, body) <- G.flattenBinds program, G.getOccString owner == name]
        case (named "helper", named "checked") of
            ([(helper, helperBody)], [(checked, checkedBody)]) ->
                case ofType (G.varType checked) of
                    RFun _ info domain result refinement -> do
                        let argument = F.symbol ("input" :: String)
                            declared = RFun argument info domain (strengthen result (uTop (F.exprReft (F.EVar argument :: F.Expr)))) refinement
                            empty = emptyTarget CmdLine.defConfig{LH.checkDerived = True, LH.checkRefinements = True, LH.totalHaskell = True, LH.noannotations = True, LH.smtsolver = Just FC.Z3}
                            source =
                                (giSrc empty)
                                    { giTarget = "AuthoredPresentation.hs"
                                    , giTargetMod = ModName Target (mkModuleName "AuthoredPresentation")
                                    , giCbs = [G.NonRec helper helperBody, G.NonRec checked checkedBody]
                                    , giDefVars = [helper, checked]
                                    }
                            spec = giSpec empty
                            targetInfo = empty{giSrc = source, giSpec = spec{gsSig = (gsSig spec){gsTySigs = [(checked, F.dummyLoc declared)]}}}
                        -- The unsigned helper and its consumer share an inference
                        -- component, so this exercises admission followed by checking.
                        (output, AI inferred, publication) <- checkTargetInfo targetInfo
                        case (o_result output, publication) of
                            (F.Safe _, Just (F.Safe _)) -> pure ()
                            _ -> assertFailure ("source judgment was not established: " ++ show (o_result output))
                        let location = G.getSrcSpan checked
                            AI templates = o_templs output
                            AI presented = o_types output
                        -- Admission has a hole here; it must not precede or duplicate
                        -- the authored annotation at the same source owner.
                        length (M.lookupDefault [] location templates) @?= 1
                        length (M.lookupDefault [] location presented) @?= 1
                        -- The returned annotation must retain the authored
                        -- dependency as a bound variable, not a display-only name.
                        case M.lookupDefault [] location inferred of
                            [(_, ty@(RFun input _ _ outputType _))] -> do
                                assertBool "the presented callable's carrier changed" (G.eqType (toType False ty) (G.varType checked))
                                assertBool "the presented dependent binder was erased" (input /= F.nonSymbol)
                                F.syms ty @?= mempty
                                let F.Reft (value, predicate) = rTypeReft outputType
                                assertBool
                                    ("the authored annotation lost its bound identity: " ++ F.showpp ty ++ "\ninput/value/predicate: " ++ show (input, value, predicate))
                                    $ F.PAtom F.Eq (F.EVar value) (F.EVar input) `elem` F.conjuncts predicate
                            _ -> assertFailure "missing authored callable annotation"
                    _ -> assertFailure "expected the checked Bool -> Bool telescope"
            _ -> assertFailure "expected the helper and its checked consumer"

qualifierConfiguration :: TestTree
qualifierConfiguration =
    testGroup
        "higher-order qualifier configuration"
        [ testCase (show (higherOrder, reflect, enumerate)) $ do
            let cfg =
                    CmdLine.defConfig
                        { LH.higherorder = higherOrder
                        , LH.reflection = reflect
                        , LH.higherorderqs = enumerate
                        , LH.smtsolver = Just FC.Z3
                        }
                info = emptyTarget cfg
                expected = F.HOI (higherOrder || reflect) enumerate
                options = fixConfig target cfg
            F.cfgHoInfo options @?= expected
            FC.sortedSolution options @?= True
            query <- void <$> cgInfoFInfo [] info (initCGI cfg info info)
            F.hoInfo query @?= expected
            F.hoInfo query @?= F.cfgHoInfo options
            case Store.decode (Store.encode query) :: Either Store.PeekException (F.FInfo ()) of
                Left failure -> assertFailure (show failure)
                Right decoded -> do
                    F.hoInfo decoded @?= expected
                    Store.encode decoded @?= Store.encode query
        | higherOrder <- [False, True]
        , reflect <- [False, True]
        , enumerate <- [False, True]
        ]

target :: FilePath
target = "HigherOrderQualifierConfig.hs"

-- Exercise the production initialization and translation with no source bindings.
emptyTarget :: LH.Config -> TargetInfo
emptyTarget cfg =
    TargetInfo
        { giSrc =
            TargetSrc
                { giTarget = target
                , giTargetMod = ModName Target (mkModuleName "HigherOrderQualifierConfig")
                , giCbs = []
                , gsTcs = []
                , gsCls = Nothing
                , giDerVars = mempty
                , giImpVars = []
                , giDefVars = []
                , giUseVars = []
                , gsExports = mempty
                , gsFiTcs = []
                , gsFiDcs = []
                , gsPrimTcs = []
                , giInstSpans = []
                }
        , giSpec =
            TargetSpec
                { gsSig = mempty
                , gsQual = SpQual [] []
                , gsData = SpData [] [] [] [] [] [] []
                , gsName =
                    SpNames
                        { gsDconsP = []
                        , gsTconsP = []
                        , gsTcEmbeds = mempty
                        , gsADTs = []
                        , gsTyconEnv = TyConMap mempty mempty mempty
                        , gsDataConIds = []
                        , gsConstructorBoxes = mempty
                        }
                , gsVars = mempty
                , gsTerm = mempty
                , gsRefl = mempty
                , gsImps = []
                , gsConfig = cfg
                }
        }
