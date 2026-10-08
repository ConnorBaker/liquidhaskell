{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module TypeLiteralIdentityTests (tests) where

import Control.Exception (evaluate, try)
import Control.Monad (forM_)
import Control.Monad.State.Strict (State, runState, state)
import qualified Data.Binary as B
import qualified Data.HashMap.Strict as M
import Data.List (isInfixOf, nub)
import GHC.Builtin.Types (charTy)
import GHC.Core.Type (mkSpecForAllTy, mkVisFunTyMany, substTyWith, typeKind)
import GHC.Types.Var.Set (isEmptyVarSet)
import qualified Language.Fixpoint.Types as F
import Language.Fixpoint.Types.Visitor (kvarsExpr)
import Language.Haskell.Liquid.Bare.Plugged (makePluggedSig)
import Language.Haskell.Liquid.Bare.ToBare (specToBare)
import qualified Language.Haskell.Liquid.Bare.Types as Bare
import qualified Language.Haskell.Liquid.GHC.Misc as GM
import Language.Haskell.Liquid.Types.Equality (compareRType)
import Language.Haskell.Liquid.Types.Errors (TError (ErrOther), UserError)
import Language.Haskell.Liquid.Types.Fresh (Freshable (..))
import Language.Haskell.Liquid.Types.RType
import Language.Haskell.Liquid.Types.RTypeOp (RTypeRepBV (..), foldReft, fromRTypeRep, rTypeReft, stripRTypeBase, toRSort, toRTypeRep)
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.Types.Types (ModName (..), ModType (..), SubsTy (subt, subtWithSort), TyConMap (..))
import qualified Liquid.GHC.API as G
import Test.Tasty (TestTree, testGroup, withResource)
import Test.Tasty.HUnit

tests :: (String -> String -> IO G.CoreProgram) -> TestTree
tests compileToCore =
    testGroup
        "type literal identity"
        [ testGroup
            "typed substitution laws"
            [ testCase "annotations on a different carrier move with the substituted coordinate" $ do
                let source = annotationCarrier oldCoordinate
                    expected = annotationCarrier newCoordinate
                    result = renameCoordinate source
                result @?= expected
            , testCase "formal predicate argument annotations retain their type owner" $ do
                assertFormalPredicate (formalPredicate newCoordinate) (renameCoordinate (formalPredicate oldCoordinate))
            , testCase "abstract predicate actual argument annotations retain their type owner" $ do
                assertAbstractApplication (abstractApplication newCoordinate) (renameCoordinate (abstractApplication oldCoordinate))
            , testCase "expression type arguments retain their annotation owner" $ do
                renameCoordinate (RExprArg (F.dummyLoc (typedExpression oldCoordinate)))
                    @?= RExprArg (F.dummyLoc (typedExpression newCoordinate))
            , testCase "a forall masks body annotations but not its own refinement" $ do
                let body = formalPredicate oldCoordinate
                    own = uReft ("vv", typedExpression oldCoordinate)
                    source = RAllT (makeRTVar oldCoordinate) body own
                    expected = RAllT (makeRTVar oldCoordinate) body (uReft ("vv", typedExpression newCoordinate))
                renameCoordinate source @?= expected
                case renameCoordinate source of
                    RAllT _ retained _ -> assertFormalPredicate body retained
                    _ -> assertFailure "substitution erased the masking forall"
            , testCase "embedding-aware substitution masks a bound annotation owner on another carrier" $ do
                let source = RAllT (makeRTVar oldCoordinate) (annotationCarrier oldCoordinate) mempty
                instantiateCoordinate source @?= source
            , testCase "embedding-aware substitution transports concrete and expression annotations" $ do
                instantiateCoordinate (annotationCarrier oldCoordinate)
                    @?= RVar otherCoordinate (uReft ("vv", typedExpressionSort F.FInt))
                instantiateCoordinate (RExprArg (F.dummyLoc (typedExpression oldCoordinate)))
                    @?= RExprArg (F.dummyLoc (typedExpressionSort F.FInt))
            , testCase "embedding-aware substitution transports formal and abstract argument annotations" $ do
                let intSort = toRSort (ofType G.intTy :: SpecType)
                    expression = typedExpressionSort F.FInt
                    concrete = RVar otherCoordinate (uReft ("vv", expression))
                    formal = RAllP (PV "formalPredicate" intSort [(intSort, "formal", expression)]) concrete
                    actual = RVar otherCoordinate (MkUReft mempty (Pr [PV "actualPredicate" NoReft [(NoReft, "formal", expression)]]))
                assertFormalPredicate formal (instantiateCoordinate (formalPredicate oldCoordinate))
                assertAbstractApplication actual (instantiateCoordinate (abstractApplication oldCoordinate))
            , testCase "forall kind and own refinement remain outside its body's masking scope" $ do
                let owner = RTVar oldCoordinate (RTVInfo "owner" (RExprArg (F.dummyLoc (typedExpression oldCoordinate))) False True)
                    source = RAllT owner (annotationCarrier oldCoordinate) (uReft ("vv", typedExpression oldCoordinate))
                case instantiateCoordinate source of
                    RAllT retained body own -> do
                        ty_var_value retained @?= oldCoordinate
                        case rtv_kind (ty_var_info retained) of
                            RExprArg expression -> F.val expression @?= typedExpressionSort F.FInt
                            _ -> assertFailure "substitution changed the owner's annotation carrier"
                        body @?= annotationCarrier oldCoordinate
                        own @?= uReft ("vv", typedExpressionSort F.FInt)
                    _ -> assertFailure "substitution erased the retained owner"
            , testCase "named expression type binders mask their bound annotation coordinate" $ do
                let expression = F.ETAbs (typedExpression oldCoordinate) (F.symbol oldCoordinate)
                    source = RVar otherCoordinate (uReft ("vv", expression))
                instantiateCoordinate source @?= source
            , testCase "retained tycon predicate metadata uses the same concrete sort interpretation" $ do
                let predicate = case formalPredicate oldCoordinate of
                        RAllP p _ -> p
                        _ -> error "formalPredicate fixture is not a predicate telescope"
                    carrier = case ofType G.intTy :: SpecType of
                        RApp c _ _ _ -> c
                        _ -> error "Int fixture is not a tycon application"
                    source = RApp (RTyCon (rtc_tc carrier) [predicate] (rtc_info carrier)) [] [] mempty
                case instantiateCoordinate source of
                    RApp c _ _ _ -> case rTyConPVs c of
                        [observed] -> do
                            ptype observed @?= toRSort (ofType G.intTy :: SpecType)
                            pargs observed @?= [(toRSort (ofType G.intTy :: SpecType), "formal", typedExpressionSort F.FInt)]
                        _ -> assertFailure "substitution erased formal tycon metadata"
                    _ -> assertFailure "substitution changed the retained tycon carrier"
            , testCase "predicate refinements transport both typed rows and their scoped body" $ do
                let source :: RTProp RTyCon RTyVar UReft
                    source =
                        RProp
                            [("row", RExprArg (F.dummyLoc (typedExpression oldCoordinate)))]
                            (RAllT (makeRTVar oldCoordinate) (annotationCarrier oldCoordinate) (uReft ("vv", typedExpression oldCoordinate)))
                    interpret = typeSort intEmbeddings . toType True
                    result = subtWithSort (Just interpret) (oldCoordinate, toRSort (ofType G.intTy :: SpecType)) source
                case result of
                    RProp rows body -> do
                        case rows of
                            [(name, RExprArg expression)] -> do
                                name @?= "row"
                                F.val expression @?= typedExpressionSort F.FInt
                            _ -> assertFailure "substitution changed the typed predicate row"
                        body @?= RAllT (makeRTVar oldCoordinate) (annotationCarrier oldCoordinate) (uReft ("vv", typedExpressionSort F.FInt))
            , testCase "an absent coordinate does not force its sort interpretation" $
                subtWithSort (Just (const (error "unused sort interpretation"))) (oldCoordinate, RHole mempty :: RSort) F.FInt @?= F.FInt
            , testCase "embedding-aware substitution preserves false refinements on another carrier" $
                instantiateCoordinate (RVar otherCoordinate falseRefinement) @?= RVar otherCoordinate falseRefinement
            , testCase "bare coordinate substitution transports nested sorts under the same scope" $ do
                let old = BTV (F.dummyLoc "bareOwner")
                    new = BTV (F.dummyLoc "bareRenamedOwner")
                    other = BTV (F.dummyLoc "bareCarrier")
                    body = RVar other (uReft ("vv", typedExpressionSort (F.FObj "bareOwner"))) :: BareType
                    replacement = RVar new NoReft :: BSort
                subt (old, replacement) (F.FAbs 0 (F.FFunc (F.FObj "bareOwner") (F.FVar 0)))
                    @?= F.FAbs 0 (F.FFunc (F.FObj "bareRenamedOwner") (F.FVar 0))
                subsTyVarMeet' (old, RVar new mempty) body
                    @?= RVar other (uReft ("vv", typedExpressionSort (F.FObj "bareRenamedOwner")))
                subsTyVarMeet' (old, RVar new mempty) (RAllT (RTVar old (RTVNoInfo True)) body mempty)
                    @?= RAllT (RTVar old (RTVNoInfo True)) body mempty
            , testCase "a forall's own abstract actual arguments are outside the body's masking scope" $ do
                let own variable = MkUReft mempty (Pr [PV "actualPredicate" NoReft [(NoReft, "formal", typedExpression variable)]])
                    source = RAllT (makeRTVar oldCoordinate) (annotationCarrier oldCoordinate) (own oldCoordinate)
                case renameCoordinate source of
                    RAllT _ body observed -> do
                        body @?= annotationCarrier oldCoordinate
                        assertAbstractApplication (RVar otherCoordinate (own newCoordinate)) (RVar otherCoordinate observed)
                    _ -> assertFailure "substitution erased the abstract refinement owner"
            ]
        , testGroup
            "constructor predicate specialization"
            [ testCase "actual arguments and retained annotations share the owner embedding" $ do
                let (constructor, catalog, _) = predicateConstructor
                    embeddings = F.tceInsert G.intTyCon F.FReal F.WithArgs mempty
                    RTV renamed = newCoordinate
                forM_ [G.intTy, G.boolTy, G.mkTyVarTy renamed] $ \actual -> do
                    let (observed, predicates) = appRTyCon embeddings catalog constructor [ofType actual :: SpecType]
                    case predicates of
                        [predicate] -> do
                            ptype predicate @?= toRSort (ofType actual :: SpecType)
                            pargs predicate @?= [(toRSort (ofType actual :: SpecType), "formal", typedExpressionSort (typeSort embeddings actual))]
                            map pargs (rTyConPVs observed) @?= map pargs predicates
                        _ -> assertFailure "specialization changed the predicate parameter count"
            , testCase "an unapplied constructor retains its formal predicate coordinates" $ do
                let (constructor, catalog, variable) = predicateConstructor
                    (_, predicates) = appRTyCon mempty catalog constructor ([] :: [SpecType])
                case predicates of
                    [predicate] -> do
                        ptype predicate @?= RVar variable NoReft
                        pargs predicate @?= [(RVar variable NoReft, "formal", typedExpression variable)]
                    _ -> assertFailure "unapplied constructor changed the predicate parameter count"
            , testCase "a recursive actual argument is interpreted once" $ do
                let (constructor, catalog, variable) = predicateConstructor
                    embeddings = F.tceInsert G.listTyCon (F.FTC F.setFTyCon) F.NoArgs mempty
                    RTV sourceVariable = variable
                    actual = G.mkTyConApp G.listTyCon [G.mkTyVarTy sourceVariable]
                    (_, predicates) = appRTyCon embeddings catalog constructor [ofType actual :: SpecType]
                case predicates of
                    [predicate] -> do
                        ptype predicate @?= toRSort (ofType actual :: SpecType)
                        pargs predicate @?= [(toRSort (ofType actual :: SpecType), "formal", typedExpressionSort (F.setSort (F.FObj (F.symbol variable))))]
                    _ -> assertFailure "recursive actual changed the predicate parameter count"
            , testCase "predicate specialization cannot erase an enclosing false refinement" $ do
                let (constructor, catalog, _) = predicateConstructor
                    embeddings = F.tceInsert G.intTyCon F.FReal F.WithArgs mempty
                    source = RApp constructor [ofType G.intTy] [] falseRefinement :: SpecType
                F.reftPred (rTypeReft (addTyConInfo embeddings catalog source)) @?= F.PFalse
            ]
        , testGroup
            "source and binary roundtrips"
            [testCase name (roundtrip literal) | (name, literal) <- literals]
        , testGroup
            "distinct indices"
            [testCase name (distinct left right) | (name, left, right) <- distinctLiterals]
        , testCase "trivial strengthening preserves every literal" $
            forM_ literals $ \(_, literal) ->
                (RLit literal `strengthen` trueReft :: SpecType) @?= RLit literal
        , testCase "different literals cannot be met" $
            rejects "Cannot strengthen distinct type literals" $
                RLit (G.NumTyLit 7) <> RLit (G.NumTyLit 8)
        , withResource kindVariables (const (pure ())) $ \getVariables ->
            let getVariable = do
                    variables <- getVariables
                    case variables of
                        variable : _ -> pure (rTyVar variable)
                        [] -> fail "missing source index binder"
             in testGroup "value refinements cannot disappear" $
                    [ testCase (name ++ " strengthening") $
                        rejects literalRefinementError (strengthen indexType refinement)
                    | (name, refinement) <- refinements
                    ]
                        ++ [ testCase "false substitution is rejected" $ do
                                variable <- getVariable
                                rejects literalRefinementError $
                                    subsTyVarMeet' (variable, indexType) (RVar variable falseRefinement)
                           , testCase "false generalized meet is rejected" $ do
                                variable <- getVariable
                                rejects literalRefinementError $
                                    strengthenRefTypeGen indexType (RVar variable falseRefinement)
                           , testCase "trivial substitution preserves the literal" $ do
                                variable <- getVariable
                                subsTyVarMeet' (variable, indexType) (RVar variable trueReft) @?= indexType
                           ]
                        ++ [ testCase (name ++ " freshness") $ do
                                variables <- getVariables
                                [variable] <- pure [v | v <- variables, G.getOccString v == name]
                                checkFreshness runtimeValue variable
                           | (name, runtimeValue) <- [("n", False), ("s", False), ("c", False), ("a", True), ("b", True), ("p", True)]
                           ]
        , withResource applicationTypes (const (pure ())) $ \getTypes ->
            testGroup "application freshness" $
                [ testCase name $ do
                    types <- getTypes
                    checkApplicationFreshness runtimeValue valueNodes (types !! index)
                | (index, (name, runtimeValue, valueNodes)) <- zip [0 ..] applicationCases
                ]
                    ++ [ testCase "constructor substitution cannot transfer a head KVar" $ do
                            types <- getTypes
                            case types of
                                constructorType : saturated : _ : _ : _ : _ : application@(RAppTy (RVar variable _) _ _) : _ -> do
                                    let constructor = fst $ runState (unFreshIds (refresh False constructorType)) 1
                                        applied = subsTyVarMeet' (variable, constructor) application
                                    toRSort applied @?= toRSort saturated
                                    rTypeReft applied @?= rTypeReft saturated
                                _ -> assertFailure "fixture lost its higher-kinded variable application"
                       ]
        , withResource embeddingTypes (const (pure ())) $ \getTypes ->
            testGroup
                "constructor-owned embedding templates"
                [ testCase "nominal carrier shares its actual argument's logical sort" $ do
                    (carrier, _, _, a, _) <- getTypes
                    let embedded = projection carrier
                        value = G.mkTyConApp carrier [a]
                    typeSort embedded value @?= typeSort mempty a
                    assertBool "logical carrier became a source value" (not (G.eqType value a))
                , testCase "forall and concrete instantiation commute with interpretation" $ do
                    (carrier, _, _, a, _) <- getTypes
                    let embedded = projection carrier
                        value = G.mkTyConApp carrier [a]
                    case a of
                        G.TyVarTy variable -> do
                            typeSort embedded (mkSpecForAllTy variable value) @?= typeSort mempty (mkSpecForAllTy variable a)
                            forM_ [G.boolTy, charTy] $ \actual ->
                                typeSort embedded (substTyWith [variable] [actual] value) @?= typeSort mempty actual
                        _ -> assertFailure "fixture lost its scoped variable"
                , testCase "two formals retain distinct actual coordinates" $ do
                    (_, pair, _, a, b) <- getTypes
                    case G.tyConTyVars pair of
                        [first, second] -> do
                            let embedded = F.tceInsert pair (F.FFunc (F.FObj (F.symbol first)) (F.FObj (F.symbol second))) F.WithArgs mempty
                            typeSort embedded (G.mkTyConApp pair [a, b]) @?= F.FFunc (typeSort mempty a) (typeSort mempty b)
                            typeSort embedded (G.mkTyConApp pair [b, a]) @?= F.FFunc (typeSort mempty b) (typeSort mempty a)
                        _ -> assertFailure "fixture lost its two formal parameters"
                , testCase "closed WithArgs embeddings remain argument-independent" $ do
                    (carrier, _, _, a, b) <- getTypes
                    let embedded = F.tceInsert carrier F.FInt F.WithArgs mempty
                    map (typeSort embedded . G.mkTyConApp carrier . pure) [a, b, G.boolTy] @?= replicate 3 F.FInt
                , testCase "nested NoArgs aggregate retains its interpreted element" $ do
                    (carrier, _, aggregate, a, _) <- getTypes
                    let embedded = F.tceInsert aggregate (F.FTC F.setFTyCon) F.NoArgs (projection carrier)
                    typeSort embedded (G.mkTyConApp aggregate [G.mkTyConApp carrier [a]]) @?= F.setSort (typeSort mempty a)
                , testCase "template substitution avoids capturing an actual sort index" $ do
                    (carrier, _, aggregate, a, _) <- getTypes
                    case G.tyConTyVars carrier of
                        [formal] -> do
                            let template = F.FAbs 0 (F.FFunc (F.FObj (F.symbol formal)) (F.FVar 0))
                                embedded = F.tceInsert aggregate (F.FVar 0) F.WithArgs (F.tceInsert carrier template F.WithArgs mempty)
                            typeSort embedded (G.mkTyConApp carrier [G.mkTyConApp aggregate [a]]) @?= F.FAbs 1 (F.FFunc (F.FVar 0) (F.FVar 1))
                        _ -> assertFailure "fixture lost its formal parameter"
                , testCase "function-valued indices do not fabricate source callbacks" $ do
                    (carrier, _, _, _, _) <- getTypes
                    let callback = mkVisFunTyMany G.boolTy G.boolTy
                        value = G.mkTyConApp carrier [callback]
                    typeSort (projection carrier) value @?= typeSort mempty callback
                    assertBool "logical carrier became callable Core" (not (G.isFunTy value))
                , testCase "concrete instantiation commutes with user-defined embeddings" $ do
                    (carrier, _, aggregate, G.TyVarTy variable, _) <- getTypes
                    let embeddings = F.tceInsert aggregate (F.FTC F.setFTyCon) F.NoArgs (F.tceInsert carrier F.FReal F.WithArgs mempty)
                        concrete = G.mkTyConApp carrier [G.boolTy]
                        predicate sort = F.PAtom F.Eq (F.ELam ("x", F.setSort sort) (F.ECst (F.EVar "x") (F.setSort sort))) (F.EVar "wanted")
                        original = RVar (RTV variable) (uReft ("vv", predicate (F.FObj (F.symbol variable)))) :: SpecType
                    forM_ [(concrete, F.FReal), (G.mkTyConApp aggregate [concrete], F.setSort F.FReal)] $ \(actual, expected) -> do
                        let result = subsTyVarMeetWith embeddings (RTV variable, ofType actual) original
                        typeSort embeddings (toType True result) @?= expected
                        F.reftPred (rTypeReft result) @?= predicate expected
                , testCase "embedding-aware instantiation covers type applications without capture" $ do
                    (carrier, _, _, G.TyVarTy variable, _) <- getTypes
                    let embeddings = F.tceInsert carrier (F.FVar 0) F.WithArgs mempty
                        old = F.FObj (F.symbol variable)
                        occurrence sort = F.ECoerc sort sort (F.ECst (F.EVar "x") sort)
                        predicate sort result = F.PAtom F.Eq (F.ETApp (occurrence sort) result) (F.EVar "wanted")
                        original = RVar (RTV variable) (uReft ("vv", predicate old (F.FAbs 0 (F.FFunc old (F.FVar 0))))) :: SpecType
                        result = subsTyVarMeetWith embeddings (RTV variable, ofType (G.mkTyConApp carrier [G.boolTy])) original
                    F.reftPred (rTypeReft result) @?= predicate (F.FVar 0) (F.FAbs 1 (F.FFunc (F.FVar 0) (F.FVar 1)))
                , testCase "embedding-aware instantiation preserves false refinements" $ do
                    (carrier, _, _, G.TyVarTy variable, _) <- getTypes
                    let embeddings = F.tceInsert carrier F.FReal F.WithArgs mempty
                        result = subsTyVarMeetWith embeddings (RTV variable, ofType (G.mkTyConApp carrier [G.boolTy])) (RVar (RTV variable) falseRefinement)
                    F.reftPred (rTypeReft result) @?= F.PFalse
                , testCase "recursive replacement interprets retained sorts exactly once" $ do
                    (_, _, aggregate, a@(G.TyVarTy variable), b) <- getTypes
                    let embeddings = F.tceInsert aggregate (F.FTC F.setFTyCon) F.NoArgs mempty
                        old = F.FObj (F.symbol variable)
                        untouched = typeSort embeddings b
                        predicate sort = F.PAtom F.Eq (F.ECst (F.EVar "x") (F.FFunc sort untouched)) (F.EVar "wanted")
                        original = RVar (RTV variable) (uReft ("vv", predicate old)) :: SpecType
                        actual = G.mkTyConApp aggregate [a]
                        result = subsTyVarMeetWith embeddings (RTV variable, ofType actual) original
                    typeSort embeddings (toType True result) @?= F.setSort old
                    F.reftPred (rTypeReft result) @?= predicate (F.setSort old)
                ]
        , withResource polyKindType (const (pure ())) $ \getType ->
            testGroup
                "kind substitution"
                [ testCase "composite GHC kinds and metadata retain the new owner" $ do
                    (_, k, f, _) <- getType
                    let new = G.setVarUnique k (G.mkUnique 'L' 17)
                        original = RTVar (RTV f) (RTVInfo "owner" (kindToRType (G.tyVarKind f)) False False)
                        result = subt (RTV k, RVar (RTV new) mempty :: RSort) original
                        expected = substTyWith [k] [G.TyVarTy new] (G.tyVarKind f)
                        RTV actual = ty_var_value result
                    assertBool "composite GHC kind retained its old owner" (G.eqType (G.tyVarKind actual) expected)
                    ty_var_info result @?= (ty_var_info original){rtv_kind = kindToRType expected}
                , testCase "freshened dependent forall telescope is closed and alpha-equivalent" $ do
                    (original, k, _, _) <- getType
                    case ofType original :: SpecType of
                        RAllT binder rest reft -> do
                            let new = RTV (G.setVarUnique k (G.mkUnique 'L' 18))
                                result = RAllT binder{ty_var_value = new} (subsTyVarMeet' (RTV k, RVar new mempty) rest) reft
                                source = toType False result
                            assertBool "freshening introduced a free kind variable" (isEmptyVarSet (G.tyCoVarsOfType source))
                            assertBool "freshening changed the interpreted source type" (G.eqType (toType False (ofType original :: SpecType)) source)
                        _ -> assertFailure "fixture lost its dependent forall telescope"
                , testCase "raw same-Unique variables retain distinct metadata coordinates" $ do
                    let k = RTV (GM.stringTyVar "k")
                        j = RTV (GM.stringTyVar "j")
                        new = RTV (G.setVarUnique (GM.stringTyVar "new") (G.mkUnique 'L' 19))
                        kind = RFun "argument" defRFInfo (RVar k mempty) (RVar j mempty) mempty :: RSort
                        original = RTVar (RTV (GM.stringTyVar "f")) (RTVInfo "owner" kind False False)
                        result = subt (k, RVar new mempty :: RSort) original
                        expected = RFun "argument" defRFInfo (RVar new mempty) (RVar j mempty) mempty
                    G.varUnique (GM.stringTyVar "k") @?= G.varUnique (GM.stringTyVar "j")
                    assertBool "fixture must distinguish raw occurrences" (k /= j)
                    ty_var_value result @?= ty_var_value original
                    ty_var_info result @?= RTVInfo "owner" expected False False
                    ty_var_info (subt (k, RVar new mempty :: RSort) (original{ty_var_info = RTVNoInfo False} :: RTVar F.Symbol F.Symbol RTyCon RTyVar)) @?= RTVNoInfo False
                , testCase "unrelated kind substitution does not force a hole replacement" $ do
                    (_, _, f, a) <- getType
                    let RTV result = subt (RTV a, RHole mempty :: RSort) (RTV f)
                    assertBool "unrelated kind changed" (G.eqType (G.tyVarKind result) (G.tyVarKind f))
                    subt (RTV a, RHole mempty :: RSort) (F.FFunc F.FInt F.boolSort) @?= F.FFunc F.FInt F.boolSort
                , testCase "freshening transports nested retained refinement sorts" $ do
                    (_, k, _, _) <- getType
                    let old = RTV k
                        new = RTV (G.setVarUnique k (G.mkUnique 'L' 20))
                        nested variable = F.FAbs 0 (F.FFunc (F.FObj (F.symbol variable)) (F.setSort (F.FObj (F.symbol variable))))
                        predicate variable =
                            let sort = nested variable
                                expression = F.ELam ("x", sort) (F.ETApp (F.ECst (F.EVar "x") sort) sort)
                             in F.PAtom F.Eq expression (F.EVar "logicalFunction")
                        original = RVar old (uReft ("vv", predicate old)) :: SpecType
                        result = subsTyVarMeet' (old, RVar new mempty) original
                    F.reftPred (rTypeReft result) @?= predicate new
                ]
        , withResource assumptionOwners (const (pure ())) $ \getOwners ->
            testGroup "authored assumption ownership" $
                [ testCase name $ do
                    owners <- getOwners
                    [owner] <- pure [v | v <- owners, G.getOccString v == name]
                    let source = ofType (G.varType owner) :: SpecType
                        cooked = plug (Bare.HsTV owner) (rawAssumption owner)
                        variables = map (ty_var_value . fst) . ty_vars . toRTypeRep
                        sourceType = toType False cooked
                        uniques = [G.varUnique variable | RTV variable <- variables cooked]
                    variables cooked @?= variables source
                    length (nub uniques) @?= length uniques
                    assertBool "source assumption has a free kind variable" (isEmptyVarSet (G.tyCoVarsOfType sourceType))
                    assertBool "source assumption changed its GHC type" (G.eqType sourceType (toType False source))
                    assertBool "source assumption is ill-kinded" (G.eqType (typeKind sourceType) (typeKind (G.varType owner)))
                | name <- ["folded", "dependent"]
                ]
                    ++ [ testCase "dictionary labels and authored dependent refinements survive" $ do
                            owners <- getOwners
                            [owner] <- pure [v | v <- owners, G.getOccString v == "folded"]
                            let representation = toRTypeRep (rawAssumption owner)
                                predicate = F.PAtom F.Eq (F.EVar "vv") (F.EApp (F.EVar "selected") (F.EVar "dictionary"))
                                authored = fromRTypeRep representation{ty_binds = ["dictionary", "values"], ty_res = ty_res representation `strengthen` uReft ("vv", predicate)}
                                cooked = toRTypeRep (plug (Bare.HsTV owner) authored)
                            ty_binds cooked @?= ["dictionary", "values"]
                            F.reftPred (rTypeReft (ty_res cooked)) @?= predicate
                       , testCase "LqTV retains its distinct schema ownership policy" $ do
                            owners <- getOwners
                            [owner] <- pure [v | v <- owners, G.getOccString v == "folded"]
                            let original = rawAssumption owner
                                variables = map (ty_var_value . fst) . ty_vars . toRTypeRep
                            variables (plug (Bare.LqTV owner) original) @?= variables original
                       ]
        ]
  where
    indexType = RLit (G.NumTyLit 7) :: SpecType
    kindVariables = do
        program <-
            compileToCore "LiteralIndex" $
                unlines
                    [ "{-# LANGUAGE ConstraintKinds, DataKinds, KindSignatures, ScopedTypeVariables #-}"
                    , "module LiteralIndex where"
                    , "import Data.Kind (Constraint, Type)"
                    , "import Data.Proxy (Proxy)"
                    , "import GHC.Exts (TYPE, RuntimeRep(IntRep))"
                    , "import GHC.TypeLits (Nat, Symbol)"
                    , "identity :: forall (n :: Nat) (s :: Symbol) (c :: Char) (a :: Type) (b :: TYPE 'IntRep) (p :: Constraint). Proxy n -> Proxy s -> Proxy c -> Proxy a -> Proxy b -> Proxy p -> ()"
                    , "identity _ _ _ _ _ _ = ()"
                    ]
        [owner] <- pure [v | (v, _) <- G.flattenBinds program, G.getOccString v == "identity"]
        let (variables, _) = G.splitForAllTyCoVars (G.varType owner)
        case variables of
            variable : _ | length variables == 6 -> do
                assertBool "substitution fixture must have a Nat-kinded index" $
                    G.eqType (G.tyVarKind variable) (typeKind (G.LitTy (G.NumTyLit 7)))
                pure variables
            _ -> assertFailure "missing source index binder" >> fail "missing source index binder"
    applicationTypes = do
        program <-
            compileToCore "FreshApplications" $
                unlines
                    [ "{-# LANGUAGE KindSignatures, ScopedTypeVariables #-}"
                    , "module FreshApplications where"
                    , "import Data.Kind (Type)"
                    , "import Data.Proxy (Proxy)"
                    , "data Pair a b = Pair a b"
                    , "applications :: forall (f :: Type -> Type) (g :: Type -> Type -> Type). Proxy IO -> Proxy (IO Bool) -> Proxy Pair -> Proxy (Pair Bool) -> Proxy (Pair Bool Bool) -> Proxy f -> Proxy (f Bool) -> Proxy g -> Proxy (g Bool) -> Proxy (g Bool Bool) -> ()"
                    , "applications _ _ _ _ _ _ _ _ _ _ = ()"
                    ]
        [owner] <- pure [v | (v, _) <- G.flattenBinds program, G.getOccString v == "applications"]
        let arguments = ty_args $ toRTypeRep (ofType (G.varType owner) :: SpecType)
            types = [argument | RApp _ parameters _ _ <- arguments, argument : _ <- [reverse parameters]]
        length types @?= length applicationCases
        pure types
    embeddingTypes = do
        program <-
            compileToCore "EmbeddingTemplates" $
                unlines
                    [ "{-# LANGUAGE KindSignatures, RoleAnnotations, ScopedTypeVariables #-}"
                    , "module EmbeddingTemplates where"
                    , "import Data.Kind (Type)"
                    , "type role Carrier nominal"
                    , "data Carrier (a :: Type) = Carrier"
                    , "data Pair (a :: Type) (b :: Type) = Pair"
                    , "data Aggregate a = Aggregate a"
                    , "witness :: forall a b. Carrier a -> Pair a b -> Aggregate a -> ()"
                    , "witness _ _ _ = ()"
                    ]
        [owner] <- pure [v | (v, _) <- G.flattenBinds program, G.getOccString v == "witness"]
        case ty_args (toRTypeRep (ofType (G.varType owner) :: SpecType)) of
            [RApp carrier [a] _ _, RApp pair [_, b] _ _, RApp aggregate _ _ _] -> pure (rtc_tc carrier, rtc_tc pair, rtc_tc aggregate, toType False a, toType False b)
            _ -> assertFailure "missing actual carrier type arguments" >> fail "missing carrier fixture"
    projection carrier = case G.tyConTyVars carrier of
        [formal] -> F.tceInsert carrier (F.FObj (F.symbol formal)) F.WithArgs mempty
        _ -> error "carrier fixture must have one formal parameter"
    polyKindType = do
        program <-
            compileToCore "DependentKinds" $
                unlines
                    [ "{-# LANGUAGE KindSignatures, PolyKinds, ScopedTypeVariables #-}"
                    , "module DependentKinds where"
                    , "import Data.Kind (Type)"
                    , "import Data.Proxy (Proxy)"
                    , "witness :: forall k (f :: k -> Type) (a :: k). Proxy (f a) -> ()"
                    , "witness _ = ()"
                    ]
        [owner] <- pure [v | (v, _) <- G.flattenBinds program, G.getOccString v == "witness"]
        let source = G.varType owner
        case G.splitForAllTyCoVars source of
            ([k, f, a], _) -> pure (source, k, f, a)
            _ -> assertFailure "missing dependent kind binders" >> fail "missing dependent kind fixture"
    assumptionOwners = do
        program <-
            compileToCore "AssumptionOwners" $
                unlines
                    [ "{-# LANGUAGE KindSignatures, PolyKinds, ScopedTypeVariables #-}"
                    , "module AssumptionOwners where"
                    , "import Data.Kind (Type)"
                    , "import Data.Proxy (Proxy)"
                    , "folded :: forall f a. Foldable f => f a -> Bool"
                    , "folded = null"
                    , "dependent :: forall k (f :: k -> Type) (a :: k). Proxy (f a) -> ()"
                    , "dependent _ = ()"
                    ]
        pure [v | (v, _) <- G.flattenBinds program]
    rawAssumption owner =
        let representation = toRTypeRep (ofType (G.varType owner) :: SpecType)
            variables = [(ty_var_value binder, RTV (GM.stringTyVar (G.getOccString variable))) | (binder, _) <- ty_vars representation, let RTV variable = ty_var_value binder]
            body = subts [(old, RVar new NoReft :: RSort) | (old, new) <- variables] (fromRTypeRep representation{ty_vars = []})
         in foldr (\(_, variable) rest -> RAllT (RTVar variable (RTVNoInfo True)) rest mempty) body variables
    plug mode = F.val . makePluggedSig False (ModName Target (G.mkModuleName "AssumptionOwners")) mempty (TyConMap mempty mempty mempty) mempty mode . F.dummyLoc

applicationCases :: [(String, Bool, Int)]
applicationCases =
    [ ("IO head", False, 0)
    , ("IO Bool", True, 2)
    , ("Pair head", False, 0)
    , ("Pair Bool retains value child", False, 1)
    , ("Pair Bool Bool", True, 3)
    , ("f head", False, 0)
    , ("f Bool", True, 2)
    , ("g head", False, 0)
    , ("g Bool retains value child", False, 1)
    , ("g Bool Bool", True, 3)
    ]

checkApplicationFreshness :: Bool -> Int -> SpecType -> Assertion
checkApplicationFreshness runtimeValue valueNodes original = do
    let run :: SpecType -> SpecType
        run t = fst $ runState (unFreshIds (refresh False t)) 1
        kvarCount :: SpecType -> Int
        kvarCount = length . foldReft False (\_ r ks -> kvarsExpr (F.reftPred (ur_reft r)) ++ ks) []
        refreshed = run original
    toRSort refreshed @?= toRSort original
    kvarCount refreshed @?= valueNodes
    if runtimeValue
        then case rTypeReft refreshed of
            F.Reft (_, F.PKVar{}) -> pure ()
            _ -> assertFailure "saturated application lost its value refinement"
        else forM_ refinements $ \(_, refinement) -> do
            let claimed = original `strengthen` refinement
                preserved = run claimed
            stripRTypeBase preserved @?= stripRTypeBase claimed
            toRSort preserved @?= toRSort claimed
            kvarCount preserved @?= valueNodes + kvarCount claimed

literals :: [(String, G.TyLit)]
literals =
    [ ("Symbol", G.StrTyLit (G.fsLit "candidate_key"))
    , ("empty Symbol", G.StrTyLit (G.fsLit ""))
    , ("former hole sentinel", G.StrTyLit (G.fsLit "$LH_RHOLE"))
    , ("Unicode Symbol", G.StrTyLit (G.fsLit "λ雪🙂"))
    , ("zero Nat", G.NumTyLit 0)
    , ("Nat", G.NumTyLit 7)
    , ("arbitrary-precision Nat", G.NumTyLit (2 ^ (200 :: Int) + 17))
    , ("Char", G.CharTyLit 'x')
    , ("Unicode Char", G.CharTyLit '🙂')
    ]

distinctLiterals :: [(String, G.TyLit, G.TyLit)]
distinctLiterals =
    [ ("Symbol contents", G.StrTyLit (G.fsLit "candidate_key"), G.StrTyLit (G.fsLit "other_key"))
    , ("Nat values", G.NumTyLit 7, G.NumTyLit 8)
    , ("Char values", G.CharTyLit 'x', G.CharTyLit 'y')
    , ("Nat and Symbol", G.NumTyLit 7, G.StrTyLit (G.fsLit "7"))
    , ("Char and Symbol", G.CharTyLit 'x', G.StrTyLit (G.fsLit "x"))
    ]

roundtrip :: G.TyLit -> Assertion
roundtrip literal = do
    let source = G.LitTy literal
        specification = ofType source :: SpecType
        bare = bareOfType source :: BareType
        restored = toType False specification
        decoded = B.decode (B.encode bare) :: BareType
    specification @?= RLit literal
    assertBool "equal literal sorts compare unequal" (toRSort specification == (RLit literal :: RSort))
    assertBool "equal literal specifications compare unequal" (compareRType specification specification)
    bare @?= RLit literal
    specToBare specification @?= bare
    decoded @?= bare
    G.eqType source restored @? "source literal identity changed"
    G.eqType (typeKind source) (typeKind restored) @? "source literal kind changed"
    case decoded of
        RLit result -> G.eqType source (G.LitTy result) @? "binary roundtrip changed source identity"
        _ -> assertFailure "binary roundtrip did not retain a type literal"

distinct :: G.TyLit -> G.TyLit -> Assertion
distinct left right = do
    let leftType = ofType (G.LitTy left) :: SpecType
        rightType = ofType (G.LitTy right) :: SpecType
        leftBare = bareOfType (G.LitTy left) :: BareType
        rightBare = bareOfType (G.LitTy right) :: BareType
    assertBool "distinct source indices collapsed" (not (G.eqType (toType False leftType) (toType False rightType)))
    assertBool "distinct refinement types compare equal" (leftType /= rightType)
    assertBool "distinct refinement sorts compare equal" (toRSort leftType /= toRSort rightType)
    assertBool "distinct specifications compare equal" (not (compareRType leftType rightType))
    assertBool "distinct literal encodings collapsed" (B.encode leftBare /= B.encode rightBare)

refinements :: [(String, RReft)]
refinements =
    [ ("False", falseRefinement)
    , ("KVar", uReft ("vv", F.PKVar (F.intKvar 0) mempty mempty))
    , ("abstract predicate", MkUReft mempty (Pr [PV "p" NoReft []]))
    ]

falseRefinement :: RReft
falseRefinement = uReft ("vv", F.PFalse)

predicateConstructor :: (RTyCon, TyConMap, RTyVar)
predicateConstructor =
    let [variable] = RTV <$> GM.tyConTyVarsDef G.listTyCon
        RApp base _ _ _ = ofType (G.mkTyConApp G.listTyCon [G.intTy]) :: SpecType
        formal = RVar variable NoReft
        predicate = PV "predicate" formal [(formal, "formal", typedExpression variable)]
        constructor = RTyCon G.listTyCon [predicate] (rtc_info base)
     in (constructor, TyConMap (M.singleton G.listTyCon constructor) mempty mempty, variable)

oldCoordinate, newCoordinate, otherCoordinate :: RTyVar
oldCoordinate = RTV (G.setVarUnique (GM.stringTyVar "annotationOwner") (G.mkUnique 'L' 41))
newCoordinate = RTV (G.setVarUnique (GM.stringTyVar "renamedAnnotationOwner") (G.mkUnique 'L' 42))
otherCoordinate = RTV (G.setVarUnique (GM.stringTyVar "otherCarrier") (G.mkUnique 'L' 43))

renameCoordinate :: SpecType -> SpecType
renameCoordinate = subsTyVarMeet' (oldCoordinate, RVar newCoordinate mempty)

typedExpression :: RTyVar -> F.Expr
typedExpression = typedExpressionSort . F.FObj . F.symbol

typedExpressionSort :: F.Sort -> F.Expr
typedExpressionSort coordinate =
    let sort = F.FAbs 0 (F.FFunc coordinate (F.FVar 0))
        value = F.ECoerc sort sort (F.ECst (F.EVar "argument") sort)
     in F.PAll [("bound", sort)] (F.ELet "retained" value (F.ELam ("local", sort) (F.ETApp (F.EVar "retained") sort)))

instantiateCoordinate :: SpecType -> SpecType
instantiateCoordinate = subsTyVarMeetWith intEmbeddings (oldCoordinate, ofType G.intTy)

intEmbeddings :: F.TCEmb G.TyCon
intEmbeddings = F.tceInsert G.intTyCon F.FInt F.WithArgs mempty

annotationCarrier :: RTyVar -> SpecType
annotationCarrier variable = RVar otherCoordinate (uReft ("vv", typedExpression variable))

formalPredicate :: RTyVar -> SpecType
formalPredicate variable =
    RAllP
        (PV "formalPredicate" (RVar variable NoReft) [(RVar variable NoReft, "formal", typedExpression variable)])
        (annotationCarrier variable)

abstractApplication :: RTyVar -> SpecType
abstractApplication variable =
    RVar otherCoordinate (MkUReft mempty (Pr [PV "actualPredicate" NoReft [(NoReft, "formal", typedExpression variable)]]))

assertFormalPredicate :: SpecType -> SpecType -> Assertion
assertFormalPredicate (RAllP expected expectedBody) (RAllP observed observedBody) = do
    pname observed @?= pname expected
    ptype observed @?= ptype expected
    pargs observed @?= pargs expected
    observedBody @?= expectedBody
assertFormalPredicate _ _ = assertFailure "substitution changed the formal predicate telescope"

assertAbstractApplication :: SpecType -> SpecType -> Assertion
assertAbstractApplication (RVar expectedVariable (MkUReft expectedReft (Pr expected))) (RVar observedVariable (MkUReft observedReft (Pr observed))) = do
    observedVariable @?= expectedVariable
    observedReft @?= expectedReft
    [(pname p, ptype p, pargs p) | p <- observed] @?= [(pname p, ptype p, pargs p) | p <- expected]
assertAbstractApplication _ _ = assertFailure "substitution changed the abstract predicate carrier"

literalRefinementError :: String
literalRefinementError = "A type-level literal cannot carry a value refinement"

newtype FreshIds a = FreshIds {unFreshIds :: State Integer a}
    deriving (Functor, Applicative, Monad)

instance Freshable FreshIds Integer where
    fresh = FreshIds (state (\n -> (n, n + 1)))

checkFreshness :: Bool -> G.TyVar -> Assertion
checkFreshness runtimeValue variable = do
    let original = rVar variable :: SpecType
        (refreshed, next) = runState (unFreshIds (refresh False original)) 1
    if runtimeValue
        then case refreshed of
            RVar same (MkUReft (F.Reft (_, F.PKVar{})) _) -> do
                same @?= rTyVar variable
                assertBool "runtime refinement was not freshened" (next > 1)
            _ -> assertFailure "runtime type variable lost refinement inference"
        else do
            refreshed @?= original
            next @?= 1
            let claimed = original `strengthen` falseRefinement
            runState (unFreshIds (refresh False claimed)) 1 @?= (claimed, 1)

rejects :: String -> SpecType -> Assertion
rejects expected expression = do
    outcome <- try (evaluate expression) :: IO (Either UserError SpecType)
    case outcome of
        Left err@ErrOther{} -> assertBool ("wrong rejection: " ++ F.showpp err) (expected `isInfixOf` F.showpp err)
        Left err -> assertFailure ("wrong error category: " ++ F.showpp err)
        Right _ -> assertFailure "a nontrivial refinement or distinct literal was silently discarded"
