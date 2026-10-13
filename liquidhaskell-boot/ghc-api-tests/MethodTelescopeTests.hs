{-# LANGUAGE OverloadedStrings #-}

module MethodTelescopeTests (tests) where

import Control.Exception (evaluate, throw, try)
import Data.Generics (everywhere, mkT)
import qualified Data.HashMap.Strict as M
import qualified Data.HashSet as S
import Data.List (isInfixOf)
import Data.Maybe (isJust, isNothing, maybeToList)
import Data.String (fromString)
import qualified GHC.Builtin.Types as G (charTy, mkListTy)
import qualified GHC.Core.Type as G (mkVisFunTyMany)
import qualified GHC.Types.Unique.Supply as Unique
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Bare.Class (classMethodField, instanceDictionaryOwners, makeMethodTypes, nominalEqualitySubstitution)
import Language.Haskell.Liquid.Bare.Plugged (makePluggedDataCon)
import qualified Language.Haskell.Liquid.Bare.Resolve as Resolve
import qualified Language.Haskell.Liquid.Bare.Types as Bare
import qualified Language.Haskell.Liquid.GHC.Misc as GM
import Language.Haskell.Liquid.Measure (constructorSourceMatch, constructorWorkerType, makeConstructorBox)
import qualified Language.Haskell.Liquid.Transforms.CoreToLogic as Logic
import Language.Haskell.Liquid.Types.DataDecl
import Language.Haskell.Liquid.Types.Dictionaries
import Language.Haskell.Liquid.Types.Errors
import Language.Haskell.Liquid.Types.Names
import Language.Haskell.Liquid.Types.PredType (dataConPSpecType)
import Language.Haskell.Liquid.Types.RType
import Language.Haskell.Liquid.Types.RTypeOp
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.Types.Types
import Language.Haskell.Liquid.UX.CmdLine (defConfig)
import qualified Liquid.GHC.API as G
import Test.Tasty (TestTree, testGroup, withResource)
import Test.Tasty.HUnit

data Fixture = Fixture G.CoreProgram G.Var G.Var G.Var SpecType

tests :: (String -> String -> IO G.CoreProgram) -> TestTree
tests compileToCore =
    withResource prepare (const (pure ())) $ \fixture ->
        testGroup
            "method telescope"
            [ predicateResolverTests
            , testCase "omitted instance context" $ do
                f@(Fixture _ _ _ _ actual) <- fixture
                _ <- check f =<< dropContext 2 actual
                pure ()
            , testCase "complete instance context" $ do
                f@(Fixture _ _ _ _ actual) <- fixture
                _ <- check f actual
                pure ()
            , testCase "nominal evidence chains have one order-independent image" $ do
                Fixture _ dictionary _ _ _ <- fixture
                let (variables, _, _, _) = G.tcSplitDFunTy (G.varType dictionary)
                [a, b] <- pure variables
                let equations = [(G.TyVarTy a, G.TyVarTy b), (G.TyVarTy a, G.charTy)]
                    checkImage pairs = do
                        substitution <- maybe (assertFailure "nominal equality chain refused" >> pure []) pure (nominalEqualitySubstitution variables pairs)
                        mapM_ (\variable -> assertBool "chain image is not Char" (maybe False (`G.eqType` G.charTy) (lookup variable substitution))) variables
                mapM_ checkImage [equations, reverse equations, [(G.TyVarTy a, G.TyVarTy b), (G.TyVarTy b, G.charTy)]]
            , testCase "nominal evidence refuses rigid conflict and recursive image" $ do
                Fixture _ dictionary _ _ _ <- fixture
                let (variables, _, _, _) = G.tcSplitDFunTy (G.varType dictionary)
                a : _ <- pure variables
                assertBool "rigid unequal carriers admitted" (isNothing (nominalEqualitySubstitution variables [(G.intTy, G.charTy)]))
                assertBool "recursive carrier image admitted" (isNothing (nominalEqualitySubstitution variables [(G.TyVarTy a, G.mkListTy (G.TyVarTy a))]))
                assertBool "non-DFun coordinate bound" (isNothing (nominalEqualitySubstitution [] [(G.TyVarTy a, G.charTy)]))
            , testCase "imported equality-chain fields agree in either source order" $
                mapM_ checkEqualityCarrier ["a ~ b, a ~ Char", "a ~ Char, a ~ b"]
            , testCase "imported admission retains context without replacing the selector" $ do
                Fixture _ dictionary selector _ actual <- fixture
                supplied <- dropContext 2 actual
                let declarations = dfromList [(dictionary, M.singleton (F.symbol (G.getOccString selector)) (RISig (F.dummyLoc supplied)))]
                    methods = makeMethodTypes mempty False declarations [] [] []
                Just obligation <- pure (lookup selector methods)
                assertBool "imported obligation became a callable selector assumption" (isNothing (getMethodType obligation))
                Just signature <- pure (tyInstance obligation)
                assertBool "imported method lost its instance context or method-local forall" (toType False (ordinarySpecType $ F.val signature) `G.eqType` toType False actual)
            , testCase "constructor source carrier retains nested polymorphic evidence" $ do
                dc <- semigroupConstructor =<< fixture
                assertBool
                    "actual Semigroup carrier rejected by its refinement projection"
                    (isJust (constructorSourceMatch dc (ofType (G.varType (G.dataConWrapId dc)))))
            , testCase "wrapper-only publication rejects an unmatched source carrier" $ do
                let dc = G.tupleDataCon G.Boxed 2
                    source = toRTypeRep (ofType (G.varType (G.dataConWrapId dc)) :: SpecType)
                    malformed = source{ty_args = ofType G.intTy : drop 1 (ty_args source)}
                    published = fst (dataConPSpecType (const (F.EVar "unused", [])) mempty True (sourceDeclaration dc malformed))
                assertBool "test premise matches the actual carrier" (isNothing (constructorSourceMatch dc (fromRTypeRep malformed)))
                rejected <-
                    try
                        ( case published of
                            [_, (_, contract)] -> evaluate (toType False contract)
                            _ -> assertFailure "unexpected constructor publication" >> pure G.intTy
                        ) ::
                        IO (Either Error G.Type)
                case rejected of
                    Left ErrDataCon{} -> pure ()
                    Left err -> assertFailure ("wrong source-carrier refusal: " ++ F.showpp err)
                    Right _ -> assertFailure "unmatched wrapper contract published without forcing the worker"
            , testCase "constructor formation aligns synthetic owners and local telescopes jointly" $ do
                f@(Fixture program _ _ _ _) <- fixture
                semigroup <- semigroupConstructor f
                [owner] <- pure [v | (v, _) <- G.flattenBinds program, G.getOccString v == "buildScoped"]
                RApp constructor _ _ _ <- pure (ty_res (toRTypeRep (ofType (G.varType owner) :: SpecType)))
                [scoped] <- pure (G.tyConDataCons (rtc_tc constructor))
                mapM_ checkConstructorOwnership [G.tupleDataCon G.Boxed 2, semigroup, scoped]
            , testCase "constructor formation rejects capture by an immediate nested binder" $ do
                Fixture program _ _ _ _ <- fixture
                [owner] <- pure [v | (v, _) <- G.flattenBinds program, G.getOccString v == "buildNested"]
                RApp constructor _ _ _ <- pure (ty_res (toRTypeRep (ofType (G.varType owner) :: SpecType)))
                [dc] <- pure (G.tyConDataCons (rtc_tc constructor))
                let actual = toRTypeRep (ofType (G.varType (G.dataConWrapId dc)) :: SpecType)
                    synthetic = toRTypeRep (everywhere (mkT (\(RTV variable) -> symbolRTyVar (F.symbol (G.getOccString variable)))) (fromRTypeRep actual))
                [RAllT actualOuter _ _] <- pure (ty_args actual)
                [RAllT sourceOuter (RAllT sourceInner body innerReft) outerReft] <- pure (ty_args synthetic)
                let captured = ty_var_value actualOuter
                    replacement = RVar captured mempty
                    badField = RAllT sourceOuter (RAllT sourceInner{ty_var_value = captured} (subsTyVarMeet' (ty_var_value sourceInner, replacement) body) innerReft) outerReft
                    supplied = sourceDeclaration dc synthetic{ty_args = [badField]}
                    plugged = F.val (makePluggedDataCon True mempty (TyConMap mempty mempty mempty) (F.dummyLoc supplied))
                rejected <-
                    try
                        ( do
                            fields <- evaluate (dcpTyArgs plugged)
                            case fields of
                                [(_, field)] -> evaluate (toType False field)
                                _ -> assertFailure "missing capture-control field" >> pure (G.varType owner)
                        ) ::
                        IO (Either Error G.Type)
                case rejected of
                    Left ErrMismatch{} -> pure ()
                    Left err -> assertFailure ("wrong capture refusal: " ++ F.showpp err)
                    Right _ -> assertFailure "source alpha-renaming captured a replacement under the immediate inner forall"
            , testCase "authored class field retains method-local quantifiers, evidence, and domain" $ do
                f@(Fixture _ _ selector _ _) <- fixture
                dc <- semigroupConstructor f
                let restrict :: SpecType -> SpecType
                    restrict (RAllT binder body reft) = RAllT binder (restrict body) reft
                    restrict (RFun name info input output reft)
                        | isClassType input = RFun name info input (restrict output) reft
                        | otherwise = RFun name info (input `strengthen` MkUReft (F.Reft (rTypeValueVar input, F.PFalse)) mempty) output reft
                    restrict t = t
                    authored = restrict (ofType (G.varType selector) :: SpecType)
                    field = classMethodField (G.dataConTyCon dc) (map rTyVar (G.dataConUnivTyVars dc)) (F.dummyLoc authored)
                [_, _, actualField] <- pure (ty_args (toRTypeRep (ofType (G.varType (G.dataConWrapId dc)) :: SpecType)))
                assertBool
                    "method-local forall or Integral evidence erased"
                    (toType False field `G.eqType` toType False actualField)
                assertBool "authored false input domain erased" (not (all isTauto field))
            , testCase "class field rejects dependence on the removed owner dictionary" $ do
                f@(Fixture _ _ selector _ _) <- fixture
                dc <- semigroupConstructor f
                let (binders, predicates, RFun _ info dictionary field reft) = bkUniv (ofType (G.varType selector) :: SpecType)
                    dependence = MkUReft (F.Reft (rTypeValueVar field, F.EApp (F.EVar "observesOwner") (F.EVar "owner"))) mempty
                    retained = field `strengthen` dependence
                    supplied = mkUnivs binders predicates (RFun "owner" info dictionary retained reft)
                assertBool "test premise lost its owner dependency" ("owner" `S.member` F.syms retained)
                refuseClassField (G.dataConTyCon dc) (map rTyVar (G.dataConUnivTyVars dc)) supplied
            , testCase "class field rejects duplicated owner coordinates" $ do
                Fixture program _ _ _ _ <- fixture
                [selector] <- pure [v | (v, _) <- G.flattenBinds program, G.getOccString v == "usePair"]
                let (binders, predicates, RFun name info (RApp constructor [left, _] parameters dictionaryReft) field reft) = bkUniv (ofType (G.varType selector) :: SpecType)
                    supplied = mkUnivs binders predicates (RFun name info (RApp constructor [left, left] parameters dictionaryReft) field reft)
                refuseClassField (rtc_tc constructor) (map (ty_var_value . fst) binders) supplied
            , testCase "constructor source carrier rejects erased runtime evidence" $ do
                dc <- semigroupConstructor =<< fixture
                let source = toRTypeRep (ofType (G.varType (G.dataConWrapId dc)) :: SpecType)
                    erase (RAllT binder (RFun _ _ evidence body _) reft)
                        | isClassType evidence = RAllT binder body reft
                    erase t = t
                assertBool
                    "nested Integral dictionary silently erased"
                    (isNothing (constructorSourceMatch dc (fromRTypeRep source{ty_args = map erase (ty_args source)})))
            , testCase "constructor source carrier preserves positional forall ownership" $ do
                let dc = G.tupleDataCon G.Boxed 2
                    source = toRTypeRep (ofType (G.varType (G.dataConWrapId dc)) :: SpecType)
                assertBool
                    "actual tuple forall ownership rejected"
                    (isJust (constructorSourceMatch dc (fromRTypeRep source)))
                assertBool
                    "permuted tuple forall ownership accepted"
                    (isNothing (constructorSourceMatch dc (fromRTypeRep source{ty_vars = reverse (ty_vars source)})))
            , testCase "worker coordinates do not capture bound source field names" $ do
                supply <- Unique.mkSplitUniqSupply 't'
                let dc = G.tupleDataCon G.Boxed 2
                    box@(ConstructorBox worker _) = Unique.initUs_ supply (makeConstructorBox dc)
                    boxes = M.singleton dc box
                    source = (toRTypeRep (ofType (G.varType (G.dataConWrapId dc)) :: SpecType)){ty_binds = map F.symbol worker}
                    interpret expression =
                        either throw id $
                            Logic.runToLogic
                                boxes
                                mempty
                                mempty
                                mempty
                                defConfig
                                (\message -> ErrOther G.noSrcSpan (fromString message))
                                (Logic.coreToLogic expression)
                    result = toRTypeRep (fst (constructorWorkerType interpret boxes dc (fromRTypeRep source)))
                assertBool
                    "fresh worker coordinate captures a source field binder"
                    (S.null (S.fromList (ty_binds source) `S.intersection` S.fromList (ty_binds result)))
            , testCase "scoped predicate and named method dictionary" $ do
                f@(Fixture _ _ _ _ actual) <- fixture
                supplied <- decorate =<< dropContext 2 actual
                answer <- check f supplied
                assertScoped supplied =<< dropContext 2 answer
            , testCase "renamed method type variable" $ do
                f@(Fixture _ _ _ _ actual) <- fixture
                supplied@(RAllT variable body reft) <- decorate =<< dropContext 2 actual
                let renamed = rTyVar (GM.symbolTyVar "sourceMethodVariable")
                answer <- check f (RAllT (makeRTVar renamed) (subts [(ty_var_value variable, RVar renamed NoReft :: RSort)] body) reft)
                assertScoped supplied =<< dropContext 2 answer
            , testCase "out-of-scope predicate is a type mismatch" $ do
                f@(Fixture _ _ _ _ actual) <- fixture
                RAllT variable (RAllP predicate _) reft <- decorate =<< dropContext 2 actual
                let (_, _, contextAndMethod) = bkUniv actual
                    escaped = mkUnivs [(variable, reft)] [] (RAllP predicate contextAndMethod)
                rejected <- try (invoke f escaped >>= evaluate . toType False) :: IO (Either Error G.Type)
                case rejected of
                    Left err@ErrMismatch{} ->
                        assertBool "wrong mismatch boundary" ("Abstract predicate is outside the scope" `isInfixOf` F.showpp err)
                    Left err -> assertFailure ("wrong error category: " ++ F.showpp err)
                    Right _ -> assertFailure "an abstract predicate escaped its type-variable scope"
            ]
  where
    checkEqualityCarrier context = do
        program <-
            compileToCore "EqualityCarrier" $
                unlines
                    [ "{-# LANGUAGE TypeFamilies, FlexibleInstances, UndecidableInstances #-}"
                    , "module EqualityCarrier where"
                    , "class Carrier a where keep :: a -> a"
                    , "instance (" ++ context ++ ") => Carrier [a] where keep x = x"
                    ]
        [dictionary] <- pure [owner | (owner, _) <- G.flattenBinds program, G.isDFunId owner]
        owners <- maybe (assertFailure "missing equality dictionary owners" >> pure []) pure (instanceDictionaryOwners program dictionary)
        [(selector, implementation)] <- pure owners
        let carrier = G.mkListTy G.charTy
            field = ofType (G.mkVisFunTyMany carrier carrier) :: SpecType
            declarations = dfromList [(dictionary, M.singleton (F.symbol (G.getOccString selector)) (RISig (F.dummyLoc field)))]
        Just imported <- pure (lookup selector (makeMethodTypes mempty False declarations [] [] []))
        mapM_
            ( \signature -> do
                let (_, _, _, body) = bkUnivClass' (ordinarySpecType $ F.val signature)
                assertBool "equality-chain field failed to specialize to String" (toType False body `G.eqType` toType False field)
            )
            (maybeToList (tyInstance imported) ++ maybeToList (tyClass imported))
        -- This is not source-carrier transport: an imported admission projection
        -- must not silently admit the same concrete schema as a local callable
        -- whose actual GHC result remains [a] under equality evidence.
        let local = lookup implementation (makeMethodTypes mempty False declarations [] [] program) >>= tyInstance
        rejected <- try (evaluate (maybe G.intTy (toType False . ordinarySpecType . F.val) local)) :: IO (Either Error G.Type)
        case rejected of
            Left ErrMismatch{} -> pure ()
            Left err -> assertFailure ("wrong local equality-carrier refusal: " ++ F.showpp err)
            Right _ -> assertFailure "unsupported local equality source-carrier transport admitted"

    prepare = do
        program <-
            compileToCore "InstanceContextMethod" $
                unlines
                    [ "{-# LANGUAGE MultiParamTypeClasses, RankNTypes #-}"
                    , "module InstanceContextMethod where"
                    , "class PairOwner left right where choosePair :: left -> right -> left"
                    , "usePair :: PairOwner left right => left -> right -> left"
                    , "usePair = choosePair"
                    , "data ScopedFields owner = ScopedFields (forall b. b -> owner) (forall b. b -> owner)"
                    , "buildScoped :: (forall b. b -> owner) -> (forall b. b -> owner) -> ScopedFields owner"
                    , "buildScoped = ScopedFields"
                    , "data NestedField owner = NestedField (forall b c. b -> c -> owner)"
                    , "buildNested :: (forall b c. b -> c -> owner) -> NestedField owner"
                    , "buildNested = NestedField"
                    , "data Wrapped key value = Wrapped value"
                    , "instance (Ord key, Semigroup value) => Semigroup (Wrapped key value) where"
                    , "  Wrapped x <> Wrapped y = Wrapped (x <> y)"
                    ]
        [dictionary] <- pure [x | (x, _) <- G.flattenBinds program, G.isDFunId x]
        owners <- maybe (fail "missing actual dictionary field owners") pure (instanceDictionaryOwners program dictionary)
        [(selector, method)] <- pure [(s, m) | (s, m) <- owners, G.getOccString s == "stimes"]
        pure (Fixture program dictionary selector method (ofType (G.varType method)))

checkConstructorOwnership :: G.DataCon -> Assertion
checkConstructorOwnership dc = do
    let actual = ofType (G.varType (G.dataConWrapId dc)) :: SpecType
        synthetic = everywhere (mkT (\(RTV variable) -> symbolRTyVar (F.symbol (G.getOccString variable)))) actual
        source = (toRTypeRep synthetic){ty_args = map mark (ty_args (toRTypeRep synthetic))}
        predicate variable = F.PAtom F.Eq (F.ECst (F.EVar "left") (F.FObj (F.symbol variable))) (F.ECst (F.EVar "right") (F.FObj (F.symbol variable)))
        mark :: SpecType -> SpecType
        mark (RAllT binder body reft) =
            let representation = toRTypeRep body
             in RAllT binder (fromRTypeRep representation{ty_res = ty_res representation `strengthen` MkUReft (F.Reft (rTypeValueVar (ty_res representation), predicate (ty_var_value binder))) mempty}) reft
        mark ty = ty
        declaration = sourceDeclaration dc source
        normalized = F.val (makePluggedDataCon True mempty (TyConMap mempty mempty mempty) (F.dummyLoc declaration))
        contracts = fst (dataConPSpecType (const (F.EVar "unused", [])) mempty True normalized)
    assertBool "test premise already has valid GHC coordinate ownership" (isNothing (constructorSourceMatch dc synthetic))
    mapM_ (\(_, contract) -> assertBool "connected source constructor ownership lost" (isJust (constructorSourceMatch dc contract))) contracts
    mapM_
        ( \(actualField, (_, normalizedField)) -> case actualField of
            RAllT binder _ _ -> F.reftPred (rTypeReft (ty_res (toRTypeRep normalizedField))) @?= predicate (ty_var_value binder)
            _ -> pure ()
        )
        (zip (ty_args (toRTypeRep actual)) (reverse (dcpTyArgs normalized)))

sourceDeclaration :: G.DataCon -> SpecRep -> DataConP
sourceDeclaration dc source = DataConP position dc (map (ty_var_value . fst) (ty_vars source)) [] [] (reverse fields) (ty_res source) False "fixture" position
  where
    position = F.loc (F.dummyLoc ())
    fields = [(makeGeneratedLogicLHName (F.intSymbol "field" i), ty) | (i, ty) <- zip [1 ..] (ty_args source)]

refuseClassField :: G.TyCon -> [RTyVar] -> SpecType -> IO ()
refuseClassField owner variables supplied = do
    rejected <- try (evaluate (toType False (classMethodField owner variables (F.dummyLoc supplied)))) :: IO (Either Error G.Type)
    case rejected of
        Left ErrOther{} -> pure ()
        Left err -> assertFailure ("wrong class-field error: " ++ F.showpp err)
        Right _ -> assertFailure "invalid class-field extraction admitted"

semigroupConstructor :: Fixture -> IO G.DataCon
semigroupConstructor (Fixture _ dictionary _ _ _) =
    case ty_res (toRTypeRep (ofType (G.varType dictionary) :: SpecType)) of
        RApp RTyCon{rtc_tc = tc} _ _ _ -> case G.tyConDataCons tc of
            [dc] -> pure dc
            _ -> fail "missing Semigroup dictionary constructor"
        _ -> fail "missing Semigroup dictionary result"

invoke :: Fixture -> SpecType -> IO SpecType
invoke (Fixture program dictionary selector method _) supplied =
    maybe (fail "missing actual method result") (pure . ordinarySpecType . F.val) $
        lookup method (makeMethodTypes mempty False declarations [] [] program) >>= tyInstance
  where
    declarations =
        dfromList
            [(dictionary, M.singleton (F.symbol (G.getOccString selector)) (RISig (F.dummyLoc supplied)))]

check :: Fixture -> SpecType -> IO SpecType
check fixture@(Fixture _ _ _ _ actual) supplied = do
    answer <- invoke fixture supplied
    -- ofType/toType makes implicit GHC arrows explicit. Compare both sides
    -- through that existing projection, retaining the complete telescope.
    assertBool
        "complete arrow/type-variable order differs from the actual GHC owner"
        (toType False answer `G.eqType` toType False actual)
    pure answer

dropContext :: Int -> SpecType -> IO SpecType
dropContext 0 ty = pure ty
dropContext n (RAllT _ body _) = dropContext n body
dropContext n (RFun _ _ _ body _) = dropContext (n - 1) body
dropContext _ _ = fail "missing instance context"

decorate :: SpecType -> IO SpecType
decorate (RAllT variable (RFun _ info evidence body reft) forallReft) =
    pure $ RAllT variable (RAllP predicate (RFun "methodDict" info evidence (body `strengthen` dependent) reft)) forallReft
  where
    predicate = PV "p" (RVar (ty_var_value variable) NoReft) []
    dependent = MkUReft (F.Reft ("vv", F.PAtom F.Eq (F.EVar "methodDict") (F.EVar "methodDict"))) (Pr [PV "p" NoReft []])
decorate _ = fail "missing method-local forall followed by Integral evidence"

assertScoped :: SpecType -> SpecType -> Assertion
assertScoped
    (RAllT expectedVariable (RAllP expectedPredicate (RFun expectedName expectedInfo expectedEvidence (RFun _ _ _ _ expectedDependent) expectedReft)) expectedForallReft)
    (RAllT variable (RAllP predicate (RFun name info evidence (RFun _ _ _ _ dependent) reft)) forallReft) = do
        ty_var_value variable @?= ty_var_value expectedVariable
        predicate @?= expectedPredicate
        name @?= expectedName
        info @?= expectedInfo
        assertBool "method evidence type changed" (toType False evidence `G.eqType` toType False expectedEvidence)
        dependent @?= expectedDependent
        reft @?= expectedReft
        forallReft @?= expectedForallReft
        assertBool
            "predicate sort escapes the method forall"
            (all ((== ty_var_value variable) . ty_var_value) (concatMap freeTyVars (ptype predicate : [s | (s, _, _) <- pargs predicate])))
assertScoped _ _ = assertFailure "method predicate, evidence, or dependent arrow moved out of its telescope position"

predicateResolverTests :: TestTree
predicateResolverTests =
    testGroup
        "lexical predicate resolution"
        [ testCase "nested predicate defaults keep both lexical owners" $
            case resolvePredicateScope (predicateScope False) of
                Right (RAllP _ (RFun _ _ (RAllP _ inner) sibling _)) -> do
                    predicateArguments inner @?= [("outer", ["outerArgument"]), ("inner", ["innerArgument"])]
                    predicateArguments sibling @?= [("outer", ["outerArgument"])]
                _ -> assertFailure "resolution changed the predicate telescope"
        , testCase "callback shadowing does not change a sibling owner" $
            case resolvePredicateScope predicateShadow of
                Right (RAllP _ (RFun _ _ (RAllP _ inner) sibling _)) -> do
                    predicateArguments inner @?= [("same", ["innerPosition"])]
                    predicateArguments sibling @?= [("same", ["outerPosition"])]
                _ -> assertFailure "resolution changed the shadowing telescope"
        , testCase "a callback predicate cannot escape into a sibling" $ do
            refusal <-
                try (evaluate (either (length . show) (length . F.showpp) (resolvePredicateScope (predicateScope True)))) ::
                    IO (Either UserError Int)
            case refusal of
                Left (ErrUnbPred span predicate) -> do
                    span @?= GM.sourcePosSrcSpan predicateSourcePos
                    assertBool "wrong predicate escaped" ("inner" `isInfixOf` show predicate)
                Left err -> assertFailure ("wrong resolver diagnostic: " ++ show err)
                Right _ -> assertFailure "callback predicate escaped its lexical body"
        , testCase "predicate resolution refuses excess actuals before substitution" $ do
            let supplied = [(NoReft, name, F.EVar name) | name <- ["first", "second"]]
                body = RVar predicateVariable (MkUReft mempty (Pr [PV "p" NoReft supplied]))
                signature = RAllP (predicateBinder "p" "declared") body
            refusal <-
                try (evaluate (either (length . show) (length . F.showpp) (resolvePredicateScope signature))) ::
                    IO (Either UserError Int)
            case refusal of
                Left err@(ErrOther span _) -> do
                    span @?= GM.sourcePosSrcSpan predicateSourcePos
                    assertBool "wrong argument-count diagnostic" ("expects at most 1 arguments, but is given 2" `isInfixOf` F.showpp err)
                Left err -> assertFailure ("wrong resolver diagnostic: " ++ show err)
                Right _ -> assertFailure "resolution silently truncated predicate actuals"
        ]

predicateSourcePos :: F.SourcePos
predicateSourcePos = F.dummyPos "PredicateOwner.hs"

resolvePredicateScope :: BareType -> Resolve.Lookup SpecType
resolvePredicateScope = Resolve.ofBareTypeE environment predicateSourcePos Nothing
  where
    unused = error "lexical predicate fixture does not use GHC lookup"
    environment = Bare.RE unused unused unused unused unused [] defConfig unused unused unused

predicateVariable :: BTyVar
predicateVariable = BTV (F.dummyLoc "a")

predicateBinder :: F.Symbol -> F.Symbol -> BPVar
predicateBinder name argument =
    PV name (RVar predicateVariable NoReft) [(RVar predicateVariable NoReft, argument, F.EVar argument)]

predicateUse :: [F.Symbol] -> BareType
predicateUse names =
    RVar predicateVariable (MkUReft mempty (Pr [PV name NoReft [] | name <- names]))

predicateScope :: Bool -> BareType
predicateScope escapes =
    RAllP
        (predicateBinder "outer" "outerArgument")
        ( RFun
            "callback"
            defRFInfo
            (RAllP (predicateBinder "inner" "innerArgument") (predicateUse ["outer", "inner"]))
            (predicateUse [if escapes then "inner" else "outer"])
            mempty
        )

predicateShadow :: BareType
predicateShadow =
    RAllP
        (predicateBinder "same" "outerPosition")
        ( RFun
            "callback"
            defRFInfo
            (RAllP (predicateBinder "same" "innerPosition") (predicateUse ["same"]))
            (predicateUse ["same"])
            mempty
        )

predicateArguments :: SpecType -> [(F.Symbol, [F.Symbol])]
predicateArguments (RVar _ (MkUReft _ (Pr predicates))) =
    [(pname predicate, [name | (_, name, _) <- pargs predicate]) | predicate <- predicates]
predicateArguments _ = []
