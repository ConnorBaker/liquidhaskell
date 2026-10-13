{-# LANGUAGE OverloadedStrings #-}

module RefinementRepresentationTests (tests) where

import Control.Monad.State.Strict (State, modify, runState)
import qualified Data.HashSet as S
import Data.Hashable (hashWithSalt)
import GHC.Builtin.Types (mkListTy)
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Bare.Resolve (txRefSort)
import Language.Haskell.Liquid.Types.PredType (mapScopedPredicateWith, pVartoRConc, substPredAtomicWith)
import Language.Haskell.Liquid.Types.RType
import Language.Haskell.Liquid.Types.RTypeOp (mapReft, toRSort)
import Language.Haskell.Liquid.Types.RefType (ofType)
import Language.Haskell.Liquid.Types.Types (TyConMap (..))
import qualified Liquid.GHC.API as G
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit

tests :: TestTree
tests =
    testGroup
        "refinement representation laws"
        [ testCase "top does not inspect a representation" $ do
            toReft (top undefined :: F.Reft) @?= F.trueReft
            toUReft (top undefined :: UReft) @?= MkUReft F.trueReft mempty
            reftBinder (top undefined :: NoReft) @?= Nothing
        , testCase "absence has no symbols or substitution action" $ do
            let absent = ofReft undefined :: NoReft
            reftBinder absent @?= Nothing
            F.syms absent @?= S.empty
            F.substr (S.singleton "vv") substitution absent @?= absent
            mapReftField undefined absent @?= absent
        , testCase "absence does not invent a value binder in a type" $ do
            let argument e = RExprArg (F.dummyLoc e)
                source = RAppTy (argument (F.EVar F.vv_)) (argument (F.EVar "outer")) NoReft :: RSort
            case F.subst1 source (F.vv_, F.EVar "image") of
                RAppTy (RExprArg left) (RExprArg right) NoReft -> do
                    F.val left @?= F.EVar "image"
                    F.val right @?= F.EVar "outer"
                _ -> assertFailure "the absence action changed the type structure"
        , testCase "concrete projection does not force abstract predicates" $ do
            let source = MkUReft concrete (Pr [undefined]) :: UReft
            toReft source @?= concrete
            reftBinder source @?= Just "root"
        , testCase "full projection retains abstract predicates" $ do
            toUReft enriched @?= enriched
            assertBool "a concrete true field is not the full predicate" $
                not (isTauto (MkUReft F.trueReft outer :: UReft))
        , testCase "injection adds no abstract predicates" $ do
            toReft (ofReft concrete :: UReft) @?= concrete
            ur_pred (ofReft concrete :: UReft) @?= mempty
            toUReft concrete @?= MkUReft concrete mempty
        , testCase "root-preserving field mapping leaves abstract predicates intact" $ do
            let mapped = mapReftField (const (F.Reft ("root", F.PFalse))) enriched
            toReft mapped @?= F.Reft ("root", F.PFalse)
            ur_pred mapped @?= outer
        , testCase "meet aligns concrete roots and retains independent predicates" $ do
            let right = MkUReft (F.Reft ("otherRoot", equality (F.EVar "otherRoot") (F.EVar "second"))) (predicate "q" "independent")
                actual = enriched `meet` right
                expected = F.meetReft concrete (ur_reft right)
            toReft actual @?= expected
            ur_pred actual @?= outer <> predicate "q" "independent"
        , testCase "application equality includes actual expressions" $
            assertBool "distinct predicate applications compare equal" $
                predicate "p" "first" /= predicate "p" "second"
        , testCase "conjunction retains distinct applications of one predicate" $ do
            let actual = predicate "p" "first" <> predicate "p" "second"
            applications actual @?= [("p", [F.EVar "first"]), ("p", [F.EVar "second"])]
        , testCase "equal conjunction views have equal hashes" $ do
            let left = predicate "p" "first" <> predicate "q" "second"
                right = predicate "q" "second" <> predicate "p" "first" <> predicate "p" "first"
            left @?= right
            hashWithSalt 17 left @?= hashWithSalt 17 right
        , testCase "substitution commutes with complete concretization" $ do
            let source = MkUReft concrete (predicate "p" "root")
                captureSubstitution = F.mkSubst [("outside", F.EVar "root")]
                names = F.syms (concretize source) `S.union` F.substSymbolsSet captureSubstitution
            concretize (F.substr names captureSubstitution source)
                @?= F.substr names captureSubstitution (concretize source)
        , testCase "conjunction commutes with complete concretization" $ do
            let left = MkUReft concrete (predicate "p" "root")
                right = MkUReft (F.Reft ("otherRoot", F.PTrue)) (predicate "q" "root")
            concretize (left `meet` right) @?= F.meetReft (concretize left) (concretize right)
        , testCase "root renaming commutes with complete concretization" $ do
            let source = MkUReft concrete (predicate "p" "root")
            concretize (renameReftRoot source "fresh") @?= F.shiftVV (concretize source) "fresh"
        , testCase "source interpretation sees the root scope in abstract actuals" $ do
            let source = MkUReft concrete (predicate "p" "root")
                (_, scopes) = runState (emapUReftVM recordScope pure source) []
            assertBool "the abstract actual escaped its refinement root" $
                any (\(variable, scope) -> variable == "root" && "root" `elem` scope) scopes
        , testCase "a use's formal label does not bind its actual expression" $ do
            let source = Pr [PV "p" NoReft [(NoReft, "formal", F.EVar "formal")]] :: Predicate
                (_, scopes) = runState (emapPredicateVM recordScope source) []
            scopes @?= [("formal", [])]
        , testCase "extra constructor predicates open in the enclosing value scope" $ do
            let extra = MkUReft F.trueReft (predicate "p" "value" <> predicate "q" "outside")
                resident :: UReft
                resident = MkUReft (F.Reft ("value", F.PTrue)) mempty
                expected = MkUReft (F.Reft ("value", F.PTrue)) (ur_pred extra)
            case ofType G.intTy :: SpecType of
                RApp constructor arguments _ _ ->
                    mapM_
                        ( \body ->
                            case F.val $
                                txRefSort (TyConMap mempty mempty mempty) mempty $
                                    F.dummyLoc (RApp constructor arguments [RProp [] body] resident) of
                                RApp _ _ properties actual -> do
                                    properties @?= []
                                    concretize actual @?= concretize expected
                                    F.syms actual @?= S.singleton "outside"
                                _ -> assertFailure "predicate promotion changed the constructor"
                        )
                        [RHole extra, RApp constructor arguments [] extra]
                _ -> assertFailure "Int did not expose its source constructor"
        , ownedPredicateScopeTests
        ]
  where
    substitution = F.mkSubst [("root", F.EVar "image")]
    equality = F.PAtom F.Eq
    concrete :: F.Reft
    concrete = F.Reft ("root", equality (F.EVar "root") (F.EVar "outside"))
    predicate :: F.Symbol -> F.Symbol -> Predicate
    predicate name actual = Pr [PV name NoReft [(NoReft, "formal", F.EVar actual)]]
    outer = predicate "p" "outside"
    enriched = MkUReft concrete outer :: UReft

ownedPredicateScopeTests :: TestTree
ownedPredicateScopeTests =
    testGroup
        "owned predicate telescope action"
        [ testCase "eliminating the outer owner preserves a shadowing callback and its actuals" $ do
            let callback = RAllP source (use "p" "nestedActual")
                body = RFun "callback" defRFInfo callback (use "p" "outerActual") mempty
                expected = RFun "callback" defRFInfo callback (use "opened" "outerActual") mempty
            eliminate (RAllP source body) @?= expected
        , testCase "owned predicate movement preserves same-spelled source term applications" $ do
            let termApplication = F.eApps (F.EVar "papp2") [F.EVar "p", F.EVar "value", F.EVar "p"]
                original = MkUReft (F.Reft ("value", termApplication)) (predicate "p" "p")
                expected = original{ur_pred = predicate "opened" "p"}
                body = mapReft (const original) boolean
            move (RAllP source body) @?= RAllP destination (mapReft (const expected) boolean)
        , testCase "only the result telescope introduces the owned binder" $ do
            let callback = RAllP source (use "p" "nestedActual")
                body = RFun "callback" defRFInfo callback (RAllP source (use "p" "outerActual")) mempty
                expected = RFun "callback" defRFInfo callback (use "opened" "outerActual") mempty
            eliminate body @?= expected
        , testCase "moving an outer owner preserves later independently shadowing binders" $ do
            let nested = RAllP source (use "p" "nestedActual")
                body = RFun "callback" defRFInfo nested (use "p" "outerActual") mempty
                expected = RAllP destination (RFun "callback" defRFInfo nested (use "opened" "outerActual") mempty)
            move (RAllP source body) @?= expected
        , testCase "constructor arguments are shadow-protected rather than owner introduction sites" $
            case ofType (mkListTy G.boolTy) :: SpecType of
                RApp constructor _ properties _ -> do
                    let nested = RAllP source (use "p" "nestedActual")
                        body = RApp constructor [nested] properties (refinement "p" "outerActual")
                        expected = RApp constructor [nested] properties (refinement "opened" "outerActual")
                    eliminate (RAllP source body) @?= expected
                _ -> assertFailure "list did not expose its source constructor"
        , testCase "atomic instantiation retains callback carriers and independently shadowing predicates" $ do
            let nested = RAllP source (use "p" "nestedActual")
                callback = RFun "argument" defRFInfo (use "p" "domainActual") nested mempty
                query = RAllP source (RFun "callback" defRFInfo callback (use "p" "outerActual") mempty)
                replacement :: F.Symbol -> UReft
                replacement actual = MkUReft (F.Reft (F.vv_, F.PAtom F.Eq (F.EVar actual) (F.EVar "outside"))) mempty
                instantiated :: F.Symbol -> SpecType
                instantiated actual = mapReft (const $ replacement actual) boolean
                expectedCallback = RFun "argument" defRFInfo (instantiated "domainActual") nested mempty
                expected = RFun "callback" defRFInfo expectedCallback (instantiated "outerActual") mempty
            substPredAtomicWith
                removeOwner
                id
                id
                (\logical _ -> logical)
                meet
                "owned callback instantiation"
                source
                [("formal", toRSort boolean)]
                (replacement "formal")
                query
                @?= expected
        ]
  where
    boolean = ofType G.boolTy :: SpecType
    source :: RPVar
    source = PV "p" (toRSort boolean) [(toRSort boolean, "formal", F.EVar "formal")]
    predicate :: F.Symbol -> F.Symbol -> Predicate
    predicate name actual = Pr [PV name NoReft [(NoReft, "formal", F.EVar actual)]]
    destination = source{pname = "opened"}
    refinement :: F.Symbol -> F.Symbol -> UReft
    refinement name actual = MkUReft F.trueReft (Pr [PV name NoReft [(NoReft, "formal", F.EVar actual)]])
    use :: F.Symbol -> F.Symbol -> SpecType
    use name actual = mapReft (const $ refinement name actual) boolean
    rename :: SpecType -> UReft -> UReft
    rename _ root = root{ur_pred = Pr [if pname predicate == "p" then predicate{pname = "opened"} else predicate | predicate <- pvars (ur_pred root)]}
    eliminate =
        mapScopedPredicateWith
            removeOwner
            source
            rename
    removeOwner binder = if pname binder == "p" then Nothing else Just (binder, pname binder)
    move =
        mapScopedPredicateWith
            (\binder -> if pname binder == "p" then Just (destination, "opened") else Just (binder, pname binder))
            source
            rename

applications :: Predicate -> [(F.Symbol, [F.Expr])]
applications (Pr ps) = [(pname p, [actual | (_, _, actual) <- pargs p]) | p <- ps]

concretize :: UReft -> F.Reft
concretize (MkUReft (F.Reft (root, body)) (Pr ps)) =
    F.Reft (root, F.pAnd (body : [pVartoRConc p (root, pargs p) | p <- ps]))

recordScope :: [F.Symbol] -> F.Symbol -> State [(F.Symbol, [F.Symbol])] F.Symbol
recordScope scope variable = modify ((variable, scope) :) >> pure variable
