{-# LANGUAGE OverloadedStrings #-}

module NativeJudgmentTests (tests) where

import qualified DefaultSchemaSharingTests
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Visitor as F
import Language.Haskell.Liquid.Bare.Elaborate (alignQueryTelescope)
import Language.Haskell.Liquid.Constraint.Generate (ConstraintObligations (..), generateConstraints)
import Language.Haskell.Liquid.Constraint.Init (initCGI)
import qualified Language.Haskell.Liquid.Constraint.Types as CG
import Language.Haskell.Liquid.Types.RType (PVarBV (..), PredicateBV (..), RTypeBV (..), SpecType, UReftBV (..), defRFInfo)
import Language.Haskell.Liquid.Types.RTypeOp (toRSort)
import Language.Haskell.Liquid.Types.RefType (ofType, strengthen, uPVar, uTop)
import Language.Haskell.Liquid.Types.Specs
import Language.Haskell.Liquid.Types.Types (CheckedPredicate (..), CheckedRefinement (..), MethodType (..), ModName (..), ModType (..), QueryTelescope (..), logicalSpecType)
import qualified Language.Haskell.Liquid.UX.CmdLine as CmdLine
import qualified Language.Haskell.Liquid.UX.Config as LH
import qualified Liquid.GHC.API as G
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase)

-- These inspect the actual generator's Horn boundary, not a second semantics
-- for Core. In particular, an inferred predicate in an iff premise is not a
-- producer, and an opaque readback does not replace a proved result contract.
tests :: (LH.Config -> TargetInfo) -> (String -> String -> IO G.CoreProgram) -> TestTree
tests emptyTarget compileToCore =
    testGroup
        "native judgment inference"
        [ testCase "alpha callback membership has an unassumed same-value producer" $ do
            program <-
                compileToCore "NativeCallbackAlphaShape" $
                    unlines
                        [ "module NativeCallbackAlphaShape where"
                        , "class CallbackDomain a where selected :: (a -> Bool) -> a -> a"
                        , "instance CallbackDomain Int where selected _ value = value"
                        , "query :: (Int -> Bool) -> Int -> Bool"
                        , "query callback value = callback value"
                        ]
            (owner, _) <- unique "$cselected" program
            (_, query) <- unique "query" program
            (left, nativeValue) <- callbackContract "q" query
            (right, rightValue) <- callbackContract "p" query
            assertBool "the alpha endpoints do not denote the same checked source value" (nativeValue == rightValue)
            let info = target "NativeCallbackAlphaShape" [] [] []
                generated = generate info owner left right
                producers =
                    [ (constraint, predicate)
                    | constraint <- CG.fixCs generated
                    , F.sr_sort (F.srhs constraint) == F.FInt
                    , predicate <- directKVars (reft $ F.srhs constraint)
                    ]
            assertBool "native membership was boxed into Bool instead of produced on the Horn RHS" (not $ null producers)
            mapM_ (checkProducer generated nativeValue) producers
            assertBool "the exact source interpretation was not checked as a separate concrete iff goal" $
                any concreteIffGoal (CG.fixCs generated)
            assertBool "the True-path witness lost its independently inferred result facts" $
                any (joinedWitness generated . fst) producers
        , testCase "opaque False guard retains both its result fact and source identity" $ do
            program <-
                compileToCore "NativeExplicitFalseShape" $
                    unlines
                        [ "module NativeExplicitFalseShape where"
                        , "{-# NOINLINE helper #-}"
                        , "helper :: Bool -> Bool"
                        , "helper _ = False"
                        , "selected :: Bool -> Bool"
                        , "selected value = value"
                        , "query :: Bool -> Bool"
                        , "query value = helper value"
                        ]
            (helper, helperBody) <- unique "helper" program
            (owner, _) <- unique "selected" program
            (_, query) <- unique "query" program
            let helperType = arrow "argument" boolean (truth False)
                source = [G.NonRec helper helperBody]
                info = target "NativeExplicitFalseShape" source [(helper, helperType)] [(helper, F.dummyLoc $ ofType $ G.varType helper)]
            telescope <- checkedTelescope (arrow "value" boolean boolean) query
            let meaning = F.eApps (F.EVar $ F.symbol helper) [F.EVar "value"]
                predicate = sourcePredicate query (arrow "value" boolean boolean) telescope meaning
                domain = guarded boolean predicate
                -- The source domain is the class endpoint: method-input
                -- contravariance opens it on the left of the native leaf.
                left = logicalSpecType $ arrow "value" (truth False) boolean
                right = RFun "value" defRFInfo domain (logicalSpecType boolean) (CheckedRefinement mempty [])
                generated = generate info owner left right
                concreteGoals = filter concreteIffGoal (CG.fixCs generated)
                witnesses = [constraint | constraint <- CG.fixCs generated, joinedWitness generated constraint]
                summaries = concatMap (joinedSummaryKVars generated) witnesses
            assertBool ("opaque source readback was never checked independently" ++ dumpJudgments generated) (not $ null concreteGoals)
            assertBool "the published native witness contains only the readback, not an inferred result" (not $ null witnesses)
            assertBool "no source result fact produces the witness summary" $
                any (\constraint -> any (`elem` summaries) (directKVars $ reft $ F.srhs constraint) && hasFalseFact (reft $ F.slhs constraint)) (CG.fixCs generated)
        ]
  where
    boolean = ofType G.boolTy :: SpecType
    integer = ofType G.intTy :: SpecType
    truth value = strengthen boolean (uTop $ F.Reft (F.vv_, if value then F.EVar F.vv_ else F.PNot $ F.EVar F.vv_))
    arrow name domain result = RFun name defRFInfo domain result mempty
    callbackContract name query = do
        let predicate = PV name (toRSort integer) []
            member = strengthen integer (MkUReft mempty $ Pr [uPVar predicate])
            callback = arrow "argument" member (truth True)
            signature = RAllP predicate $ arrow "callback" callback (arrow "value" member boolean)
        telescope <- checkedTelescope signature query
        let source = sourcePredicate query signature telescope (F.eApps (F.EVar "callback") [F.EVar "value"])
        nativeValue <- case lookup "value" (queryValueOwners telescope) of
            Just identifier -> pure $ F.symbol identifier
            Nothing -> assertFailure "the checked query lost its exact value owner" >> fail "value owner"
        pure
            ( RAllP predicate $
                RFun
                    "callback"
                    defRFInfo
                    (logicalSpecType callback)
                    (RFun "value" defRFInfo (guarded member source) (logicalSpecType member) (CheckedRefinement mempty []))
                    (CheckedRefinement mempty [])
            , nativeValue
            )
    guarded ty predicate = case logicalSpecType ty of
        RApp constructor arguments properties refinement -> RApp constructor arguments properties refinement{checkedPredicates = [predicate]}
        _ -> error "native fixture requires a base carrier"
    sourcePredicate query signature telescope meaning =
        CheckedPredicate
            query
            signature
            telescope
            (F.subst rootAction meaning)
            [(identifier, F.subst rootAction $ F.EVar name) | (name, identifier) <- queryValueOwners telescope, not $ G.isCoVar identifier]
            mempty
            []
            []
      where
        -- The query's value formal denotes the resident refinement root,
        -- not the enclosing arrow's independently refreshed value owner.
        -- Keep both representations under this same checked owner action.
        rootAction = F.mkSubst [("value", F.EVar F.vv_)]
    checkedTelescope signature query = either (\message -> assertFailure message >> fail message) pure (alignQueryTelescope signature query)
    unique name program = case [(owner, body) | (owner, body) <- G.flattenBinds program, G.getOccString owner == name] of
        [binding] -> pure binding
        bindings -> assertFailure ("expected one actual Core owner " ++ name ++ ", found " ++ show (length bindings)) >> fail name
    target name source signatures reflected =
        let empty = emptyTarget CmdLine.defConfig{LH.checkDerived = True, LH.checkRefinements = True, LH.totalHaskell = True, LH.higherorder = True, LH.noannotations = True}
            spec = giSpec empty
            constructors = [(G.dataConWorkId constructor, F.dummyLoc $ truth value) | (constructor, value) <- [(G.trueDataCon, True), (G.falseDataCon, False)]]
         in empty
                { giSrc = (giSrc empty){giTarget = name ++ ".hs", giTargetMod = ModName Target (G.mkModuleName name), giCbs = source, giDefVars = concatMap G.bindersOf source}
                , giSpec =
                    spec
                        { gsSig = (gsSig spec){gsTySigs = [(owner, F.dummyLoc ty) | (owner, ty) <- signatures], gsRefSigs = reflected}
                        , gsName = (gsName spec){gsTcEmbeds = F.tceFromList [(G.intTyCon, (F.FInt, F.NoArgs)), (G.boolTyCon, (F.boolSort, F.NoArgs))]}
                        , gsImps = [(F.symbol $ G.dataConWorkId constructor, F.boolSort) | constructor <- [G.trueDataCon, G.falseDataCon]]
                        , gsData = (gsData spec){gsCtors = constructors}
                        }
                }
    generate info owner left right =
        let methods = [(owner, MT (Just $ F.dummyLoc left) (Just $ F.dummyLoc right) Nothing)]
            obligations = ConstraintObligations (giCbs $ giSrc info) methods mempty []
         in snd $ generateConstraints (initCGI (LH.getConfig info) info) (DefaultSchemaSharingTests.schemas info info) [] info obligations

reft :: F.SortedReft -> F.Expr
reft = F.reftPred . F.sr_reft

directKVars :: F.Expr -> [F.KVar]
directKVars expression = [predicate | F.PKVar predicate _ _ <- F.conjuncts expression]

concreteIffGoal :: CG.FixSubC -> Bool
concreteIffGoal constraint = F.sr_sort (F.srhs constraint) == F.boolSort && any concreteIff (F.conjuncts $ reft $ F.srhs constraint)

concreteIff :: F.Expr -> Bool
concreteIff expression@F.PIff{} = F.isConc expression
concreteIff _ = False

activeRefinements :: CG.CGInfo -> CG.FixSubC -> [F.Expr]
activeRefinements generated constraint =
    [reft refinement | identifier <- F.elemsIBindEnv (F.senv constraint), let (_, refinement, _) = F.lookupBindEnv identifier (CG.binds generated)]

joinedWitness :: CG.CGInfo -> CG.FixSubC -> Bool
joinedWitness generated = not . null . joinedSummaryKVars generated

joinedSummaryKVars :: CG.CGInfo -> CG.FixSubC -> [F.KVar]
joinedSummaryKVars generated constraint =
    concat
        [ directKVars expression
        | expression <- activeRefinements generated constraint
        , any concreteIff (F.conjuncts expression)
        ]

checkProducer :: CG.CGInfo -> F.Symbol -> (CG.FixSubC, F.KVar) -> IO ()
checkProducer generated nativeValue (constraint, predicate) = do
    assertBool "the RHS membership was assumed in Gamma before its producer" $
        all (notElem predicate . F.kvarsExpr) (activeRefinements generated constraint)
    assertBool ("the membership producer was not pinned to the same native source value" ++ dumpJudgments generated) $
        any isPinned (F.conjuncts $ reft $ F.slhs constraint)
  where
    root = F.reftBind $ F.sr_reft $ F.slhs constraint
    isPinned (F.PAtom F.Eq (F.EVar left) (F.EVar right)) = left == root && right == nativeValue && left /= right
    isPinned _ = False

hasFalseFact :: F.Expr -> Bool
hasFalseFact = any isFalse . F.conjuncts
  where
    isFalse (F.PNot F.EVar{}) = True
    isFalse F.PFalse = True
    isFalse _ = False

dumpJudgments :: CG.CGInfo -> String
dumpJudgments generated =
    unlines $
        ""
            : concat
                [ ["constraint " ++ show index ++ ": " ++ F.showpp (F.slhs constraint) ++ " <: " ++ F.showpp (F.srhs constraint)]
                    ++ ["  " ++ F.showpp name ++ " : " ++ F.showpp refinement | identifier <- F.elemsIBindEnv (F.senv constraint), let (name, refinement, _) = F.lookupBindEnv identifier (CG.binds generated)]
                | (index, constraint) <- zip [(1 :: Int) ..] (CG.fixCs generated)
                ]
