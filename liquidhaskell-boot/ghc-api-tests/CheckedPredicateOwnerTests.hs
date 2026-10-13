{-# LANGUAGE OverloadedStrings #-}

module CheckedPredicateOwnerTests (tests) where

import Control.Exception (throw)
import Data.Either (isLeft)
import Data.Generics (everywhere, mkT)
import qualified Data.HashSet as S
import Data.String (fromString)
import qualified GHC.Builtin.Types as G (wordTy, wordTyCon)
import qualified GHC.Core.Type as G (getTyVar_maybe, piResultTy, piResultTys)
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Bare.Elaborate (alignQueryTelescope, freshenQueryTelescope, interpretCheckedPredicate, renameCheckedPredicateOwner)
import Language.Haskell.Liquid.Constraint.Split (substCheckedTyVar)
import qualified Language.Haskell.Liquid.GHC.Misc as GM
import qualified Language.Haskell.Liquid.Transforms.CoreToLogic as Logic
import Language.Haskell.Liquid.Types.Errors (TError (ErrOther))
import Language.Haskell.Liquid.Types.RType (IsReft (renameReftRoot), RTyVar (..), RTypeBV (RAllT, RFun, RVar), SpecType, UReftBV (..), ty_var_value)
import Language.Haskell.Liquid.Types.RTypeOp (fromRTypeRep, toRTypeRep, ty_args, ty_binds, ty_vars)
import Language.Haskell.Liquid.Types.RefType (ofType, toType, typeSort)
import Language.Haskell.Liquid.Types.Types (CheckedPredicate (..), CheckedRefinement (..), QueryTelescope (..), checkedOrdinary, renameCheckedRoot)
import Language.Haskell.Liquid.UX.CmdLine (defConfig)
import qualified Liquid.GHC.API as G
import Test.Tasty (TestTree, testGroup, withResource)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

tests :: (String -> String -> IO G.CoreProgram) -> TestTree
tests compileToCore = withResource prepare (const (pure ())) $ \fixture ->
    testGroup
        "checked predicate owner action"
        [ testCase "resident owner action transports both representations" $ do
            checked <- fixture
            resident <-
                either (\message -> assertFailure message >> fail message) pure $
                    renameCheckedPredicateOwner G.intTy "queryRoot" "residentRoot" checked
            predicateReadback resident @?= F.EVar "residentRoot"
            map snd (predicateDefinitions resident) @?= [F.EVar "residentRoot"]
            map fst (predicateDefinitions resident) @?= map snd (queryValueOwners (predicateTelescope checked))
            assertBool "owner presentation changed the nominal checked Core" $
                G.eqType (G.exprType (predicateCore resident)) (G.exprType (predicateCore checked))
        , testCase "equal logical sorts do not license a different nominal owner" $ do
            checked <- fixture
            let embeddings =
                    F.tceInsert G.wordTyCon F.intSort F.NoArgs $
                        F.tceInsert G.intTyCon F.intSort F.NoArgs mempty
            typeSort embeddings G.intTy @?= typeSort embeddings G.wordTy
            assertBool "Word presentation borrowed checked Int ownership" $
                isLeft (renameCheckedPredicateOwner G.wordTy "queryRoot" "residentRoot" checked)
        , testCase "an unrelated logical name cannot borrow a checked owner" $ do
            checked <- fixture
            assertBool "an absent source owner was admitted" $
                isLeft (renameCheckedPredicateOwner G.intTy "notTheOwner" "residentRoot" checked)
        , testCase "root alignment preserves free coordinates under a quantified owner" $ do
            checked <- fixture
            let body =
                    F.PAll [("r", F.intSort)] $
                        F.PAnd
                            [ F.PAtom F.Eq (F.EVar "v") (F.EVar "r")
                            , F.PAtom F.Eq (F.EVar "r##0") (F.EVar "r")
                            ]
                source =
                    checked
                        { predicateReadback = body
                        , predicateDefinitions = [(owner, body) | (owner, _) <- predicateDefinitions checked]
                        }
                original = CheckedRefinement (MkUReft (F.Reft ("v", F.PTrue)) mempty) [source]
                renamed = renameCheckedRoot original "r"
                expected = F.subst1 body ("v", F.EVar "r")
            checkedOrdinary renamed @?= renameReftRoot (checkedOrdinary original) "r"
            F.syms (checkedOrdinary renamed) @?= S.singleton "r##0"
            case checkedPredicates renamed of
                [resident] -> do
                    predicateReadback resident @?= expected
                    map snd (predicateDefinitions resident) @?= [expected]
                    F.syms (predicateReadback resident) @?= S.fromList ["r", "r##0"]
                    case predicateReadback resident of
                        F.PAll [(freshOwner, _)] _ ->
                            assertBool "fresh owner captured a free coordinate" $
                                freshOwner /= "r" && freshOwner /= "r##0"
                        _ -> assertFailure "expected the quantified source predicate"
                _ -> assertFailure "expected one retained source conjunct"
        , testCase "polymorphic owner action reinterprets in the authored sort coordinates" $ do
            program <-
                compileToCore "PolymorphicCheckedOwner" $
                    unlines
                        [ "module PolymorphicCheckedOwner where"
                        , "query :: a -> a"
                        , "query input = input"
                        ]
            case [(owner, core) | (owner, core) <- G.flattenBinds program, G.getOccString owner == "query"] of
                [(owner, core)] -> do
                    let authored = everywhere (mkT symbolic) (ofType (G.varType owner) :: SpecType)
                        source = fromRTypeRep (toRTypeRep authored){ty_binds = ["queryRoot"]}
                    telescope <- either (\message -> assertFailure message >> fail message) pure (alignQueryTelescope source core)
                    case (queryTypeOwners telescope, queryValueOwners telescope) of
                        ([(sourceVariable, actualType)], [("queryRoot", actual)]) -> do
                            actualVariable <- maybe (assertFailure "expected a native type owner" >> fail "native type owner") pure (G.getTyVar_maybe actualType)
                            assertBool "fixture did not distinguish the type namespaces" (F.symbol sourceVariable /= F.symbol actualVariable)
                            let nativeMeaning = F.ECst (F.EVar "queryRoot") (F.FObj (F.symbol actualVariable))
                                authoredMeaning = F.ECst (F.EVar "queryRoot") (F.FObj (F.symbol sourceVariable))
                                checked = CheckedPredicate core source telescope authoredMeaning [(actual, nativeMeaning)] mempty [] []
                                interpret embeddings definitions expression =
                                    either throw id $
                                        Logic.runToLogic
                                            mempty
                                            embeddings
                                            mempty
                                            mempty
                                            defConfig
                                            (\message -> ErrOther G.noSrcSpan (fromString message))
                                            (Logic.coreToLogicWithDefinitions definitions expression)
                            fst (interpretCheckedPredicate interpret checked) @?= authoredMeaning
                            resident <-
                                either (\message -> assertFailure message >> fail message) pure $
                                    renameCheckedPredicateOwner (G.mkTyVarTy sourceVariable) "queryRoot" "residentRoot" checked
                            fst (interpretCheckedPredicate interpret resident) @?= predicateReadback resident
                            predicateReadback resident @?= F.ECst (F.EVar "residentRoot") (F.FObj (F.symbol sourceVariable))
                        _ -> assertFailure "expected one retained nominal type and value owner"
                _ -> assertFailure "expected one actual polymorphic source query"
        , testCase "query forall alignment opens Core at the transported nominal owner" $ do
            program <-
                compileToCore "CheckedQueryAlpha" $
                    unlines
                        [ "{-# LANGUAGE ExplicitForAll #-}"
                        , "module CheckedQueryAlpha where"
                        , "query :: forall a. (a -> a) -> a -> Bool"
                        , "query _ _ = False"
                        , "target :: forall b. (b -> b) -> b -> Bool"
                        , "target _ _ = False"
                        ]
            case ([(owner, core) | (owner, core) <- G.flattenBinds program, G.getOccString owner == "query"], [owner | (owner, _) <- G.flattenBinds program, G.getOccString owner == "target"]) of
                ([(owner, core)], [target]) -> do
                    let source = fromRTypeRep (toRTypeRep (ofType (G.varType owner) :: SpecType)){ty_binds = ["callback", "input"]}
                    telescope <- either (\message -> assertFailure message >> fail message) pure (alignQueryTelescope source core)
                    case (ty_vars (toRTypeRep source), ty_vars (toRTypeRep (ofType (G.varType target) :: SpecType))) of
                        ([(sourceBinder, _)], [(targetBinder, _)]) -> do
                            let original@(RTV originalOwner) = ty_var_value sourceBinder
                                destination@(RTV destinationOwner) = ty_var_value targetBinder
                                definitions = [(actual, F.EVar logical) | (logical, actual) <- queryValueOwners telescope]
                                checked = CheckedPredicate core source telescope F.PFalse definitions mempty [] []
                                endpoint = RVar original (CheckedRefinement mempty [checked])
                            assertBool "source compilation did not produce independent nominal owners" (originalOwner /= destinationOwner)
                            case substCheckedTyVar (original, destination) endpoint of
                                RVar _ refinement -> case checkedPredicates refinement of
                                    [aligned] -> do
                                        let signature = toRTypeRep (predicateSignature aligned)
                                            openedOwner = G.mkTyVarTy destinationOwner
                                            openedCoreType = G.piResultTy (G.exprType (predicateCore aligned)) openedOwner
                                        map (ty_var_value . fst) (ty_vars signature) @?= [destination]
                                        assertBool "opened Core and retained query signature disagree nominally" $
                                            G.eqType openedCoreType (toType False (fromRTypeRep signature{ty_vars = []}))
                                        case (ty_args signature, queryTypeOwners telescope, lookup "callback" (queryValueOwners telescope)) of
                                            (callbackDomain : _, [(nativeOwner, nativeType)], Just callback) -> do
                                                nativeVariable <- maybe (assertFailure "expected a native type coordinate" >> fail "native type coordinate") pure (G.getTyVar_maybe nativeType)
                                                let actualCallback = G.substTyWith [nativeVariable] [openedOwner] (G.varType callback)
                                                assertBool "transported callback cannot be passed to opened Core" $
                                                    G.eqType (toType False callbackDomain) actualCallback
                                                map fst (queryTypeOwners (predicateTelescope aligned)) @?= [destinationOwner]
                                                assertBool "fixture lost its original nominal coordinate" (nativeOwner == originalOwner)
                                            _ -> assertFailure "expected one nominal owner and a callback domain"
                                    _ -> assertFailure "expected one checked query"
                                _ -> assertFailure "expected the transported endpoint carrier"
                        _ -> assertFailure "expected independent single-forall query signatures"
                _ -> assertFailure "expected independently compiled query and target bindings"
        , testCase "query kind alignment transports dependent owners before opening Core" $ do
            program <-
                compileToCore "CheckedQueryKinds" $
                    unlines
                        [ "{-# LANGUAGE ExplicitForAll, PolyKinds, KindSignatures #-}"
                        , "module CheckedQueryKinds where"
                        , "import Data.Kind (Type)"
                        , "query :: forall k (f :: k -> Type) (a :: k). f a -> Bool"
                        , "query _ = False"
                        , "target :: forall j (g :: j -> Type) (b :: j). g b -> Bool"
                        , "target _ = False"
                        ]
            case ([(owner, core) | (owner, core) <- G.flattenBinds program, G.getOccString owner == "query"], [owner | (owner, _) <- G.flattenBinds program, G.getOccString owner == "target"]) of
                ([(owner, core)], [target]) -> do
                    let source = fromRTypeRep (toRTypeRep (ofType (G.varType owner) :: SpecType)){ty_binds = ["input"]}
                    telescope <- either (\message -> assertFailure message >> fail message) pure (alignQueryTelescope source core)
                    case (ty_vars (toRTypeRep source), ty_vars (toRTypeRep (ofType (G.varType target) :: SpecType))) of
                        ((sourceBinder, _) : _, (targetBinder, _) : _) -> do
                            let original@(RTV originalOwner) = ty_var_value sourceBinder
                                destination@(RTV destinationOwner) = ty_var_value targetBinder
                                definitions = [(actual, F.EVar logical) | (logical, actual) <- queryValueOwners telescope]
                                checked = CheckedPredicate core source telescope F.PFalse definitions mempty [] []
                            assertBool "source kind owners were not independent" (originalOwner /= destinationOwner)
                            case substCheckedTyVar (original, destination) (RVar original (CheckedRefinement mempty [checked])) of
                                RVar _ refinement -> case checkedPredicates refinement of
                                    [aligned] -> do
                                        let signature = toRTypeRep (predicateSignature aligned)
                                            alignedOwners = queryTypeOwners (predicateTelescope aligned)
                                            nativeArguments = [G.mkTyVarTy coordinate | (coordinate, _) <- alignedOwners]
                                            openedCoreType = G.piResultTys (G.exprType core) nativeArguments
                                        length alignedOwners @?= 3
                                        map (ty_var_value . fst) (ty_vars signature) @?= map (RTV . fst) alignedOwners
                                        assertBool "dependent query kinds disagree with opened Core" $
                                            G.eqType openedCoreType (toType False (fromRTypeRep signature{ty_vars = []}))
                                        assertBool "old kind coordinate escaped the transported telescope" $
                                            not (originalOwner `G.elemVarSet` G.tyCoVarsOfType openedCoreType)
                                        mapM_
                                            ( \((before, native), (after, retained)) -> do
                                                assertBool "native formal type image changed" (G.eqType native retained)
                                                assertBool "authored dependent owner kind was not transported" $
                                                    G.eqType (G.tyVarKind after) (G.substTyWith [originalOwner] [G.mkTyVarTy destinationOwner] (G.tyVarKind before))
                                            )
                                            (zip (queryTypeOwners telescope) alignedOwners)
                                    _ -> assertFailure "expected one checked kind-dependent query"
                                _ -> assertFailure "expected the transported kind-coordinate endpoint"
                        _ -> assertFailure "expected explicit dependent kind telescopes"
                _ -> assertFailure "expected independently compiled kind-dependent source queries"
        , testCase "query alpha alignment reaches a forall after a value owner" $ do
            program <-
                compileToCore "CheckedInterleavedAlpha" $
                    unlines
                        [ "{-# LANGUAGE ExplicitForAll, RankNTypes #-}"
                        , "module CheckedInterleavedAlpha where"
                        , "query :: Int -> forall a. (a -> a) -> a -> Bool"
                        , "query _ = \\_ _ -> False"
                        , "target :: Int -> forall b. (b -> b) -> b -> Bool"
                        , "target _ = \\_ _ -> False"
                        ]
            case ([(owner, core) | (owner, core) <- G.flattenBinds program, G.getOccString owner == "query"], [(owner, core) | (owner, core) <- G.flattenBinds program, G.getOccString owner == "target"]) of
                ([(owner, core)], [(target, targetCore)]) -> do
                    let source = freshenQueryTelescope False [] (ofType (G.varType owner) :: SpecType)
                        targetSignature = freshenQueryTelescope False [] (ofType (G.varType target) :: SpecType)
                    telescope <- either (\message -> assertFailure message >> fail message) pure (alignQueryTelescope source core)
                    targetTelescope <- either (\message -> assertFailure message >> fail message) pure (alignQueryTelescope targetSignature targetCore)
                    case (queryTypeOwners telescope, queryTypeOwners targetTelescope) of
                        ([(originalOwner, _)], [(destinationOwner, _)]) -> do
                            let definitions = [(actual, F.EVar logical) | (logical, actual) <- queryValueOwners telescope]
                                checked = CheckedPredicate core source telescope F.PFalse definitions mempty [] []
                                endpoint = RVar (RTV originalOwner) (CheckedRefinement mempty [checked])
                            assertBool "interleaved source owners were not independent" (originalOwner /= destinationOwner)
                            case substCheckedTyVar (RTV originalOwner, RTV destinationOwner) endpoint of
                                RVar _ refinement -> case checkedPredicates refinement of
                                    [aligned] -> case predicateSignature aligned of
                                        RFun _ _ _ (RAllT binder body _) _ -> do
                                            ty_var_value binder @?= RTV destinationOwner
                                            let opened = G.piResultTy (G.piResultTy (G.exprType core) G.intTy) (G.mkTyVarTy destinationOwner)
                                            assertBool "interleaved opened Core retained its old type owner" (G.eqType opened (toType False body))
                                            assertBool "old query coordinate escaped into the interleaved result" $
                                                not (originalOwner `G.elemVarSet` G.tyCoVarsOfType (toType False body))
                                        _ -> assertFailure "expected a type binder after the first value argument"
                                    _ -> assertFailure "expected one interleaved source query"
                                _ -> assertFailure "expected the transported endpoint"
                        _ -> assertFailure "expected one interleaved nominal type owner per source"
                _ -> assertFailure "expected independently compiled interleaved source queries"
        ]
  where
    symbolic :: RTyVar -> RTyVar
    symbolic (RTV variable) = RTV (GM.symbolTyVar (F.symbol variable))
    prepare = do
        program <-
            compileToCore "CheckedOwner" $
                unlines
                    [ "module CheckedOwner where"
                    , "query :: Int -> Int"
                    , "query input = input"
                    ]
        case [(owner, core) | (owner, core) <- G.flattenBinds program, G.getOccString owner == "query"] of
            [(owner, core)] -> do
                let source = fromRTypeRep (toRTypeRep (ofType (G.varType owner) :: SpecType)){ty_binds = ["queryRoot"]}
                telescope <- either (\message -> assertFailure message >> fail message) pure (alignQueryTelescope source core)
                let definitions = [(actual, F.EVar logical) | (logical, actual) <- queryValueOwners telescope]
                pure (CheckedPredicate core source telescope (F.EVar "queryRoot") definitions mempty [] [])
            _ -> assertFailure "expected one actual source query" >> fail "source query"
