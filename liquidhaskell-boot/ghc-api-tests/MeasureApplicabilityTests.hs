{-# LANGUAGE OverloadedStrings #-}

module MeasureApplicabilityTests (tests) where

import ConstraintGenerationTests (emptyTarget)
import qualified Control.Exception as Ex
import qualified Data.HashMap.Strict as HM
import Data.List (isInfixOf)
import Data.Maybe (isJust, isNothing)
import qualified GHC.Builtin.Types as G
import qualified GHC.Core as G (CoreProgram, flattenBinds)
import qualified GHC.Core.DataCon as G
import qualified GHC.Core.Subst as G (mkEmptySubst)
import qualified GHC.Core.TyCo.Compare as G (eqType)
import qualified GHC.Core.TyCon as G (tyConDataCons)
import qualified GHC.Core.Type as G
import qualified GHC.Types.Basic as G
import qualified GHC.Types.Id as G
import qualified GHC.Types.Name as G (getOccString)
import qualified GHC.Types.Var as G (TyVar)
import qualified GHC.Types.Var.Env as G (mkInScopeSet)
import qualified GHC.Types.Var.Set as G (mkVarSet)
import qualified Language.Fixpoint.SortCheck as SortCheck
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Bare.Check (checkTargetSpec)
import Language.Haskell.Liquid.Measure
import Language.Haskell.Liquid.Types.Errors (TError (..), UserError)
import Language.Haskell.Liquid.Types.Names
import Language.Haskell.Liquid.Types.RType (NoReftBV (..), PVarBV (..), PredicateBV (..), RRType, RTypeBV (RAllT), SpecType, UReftBV (..), makeRTVar)
import Language.Haskell.Liquid.Types.RTypeOp (mapRBase, rFun, stripRTypeBase)
import Language.Haskell.Liquid.Types.RefType (ofType, rTyVar, rTypeSort, strengthen, toType)
import Language.Haskell.Liquid.Types.Specs
import Language.Haskell.Liquid.Types.Types
import Language.Haskell.Liquid.UX.CmdLine (defConfig)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit

scopedEquationFields :: String
scopedEquationFields =
    unlines
        [ "{-# LANGUAGE GADTs #-}"
        , "module ScopedEquationFields where"
        , "data Hidden a = Hidden (Int -> Int)"
        , "selectHidden :: Hidden a -> Int"
        , "selectHidden (Hidden callback) = callback 0"
        , "newtype Wrapped a = Wrapped a"
        , "selectWrapped :: Wrapped a -> a"
        , "selectWrapped (Wrapped value) = value"
        , "data Indexed a where Indexed :: Int -> Indexed (Maybe a)"
        , "selectIndexed :: Indexed a -> Int"
        , "selectIndexed (Indexed value) = value"
        ]

fixtureConstructor :: G.CoreProgram -> String -> IO G.DataCon
fixtureConstructor program name = case [owner | (owner, _) <- G.flattenBinds program, G.getOccString owner == name] of
    [owner] -> case G.splitFunTys (snd (G.splitForAllTyCoVars (G.varType owner))) of
        (argument : _, _) -> case G.splitTyConApp_maybe (G.irrelevantMult argument) of
            Just (constructor, _) -> case G.tyConDataCons constructor of
                [dataConstructor] -> pure dataConstructor
                _ -> fail ("fixture requires exactly one constructor: " ++ name)
            _ -> fail ("fixture lost source constructor carrier: " ++ name)
        _ -> fail ("fixture lost its input telescope: " ++ name)
    _ -> fail ("fixture lost its source owner: " ++ name)

tests :: (String -> String -> IO G.CoreProgram) -> TestTree
tests compileToCore =
    testGroup
        "measure equation applicability"
        [ testCase "only supported nonuniform authored constructor schemas are deferred" $ do
            let dc = G.nilDataCon
                list ty = G.mkTyConApp G.listTyCon [ty]
                equation = Def (name dc) dc Nothing [] (P F.PTrue)
                concrete = measureSignature (ofType (list G.word8Ty))
                generic = universal (G.dataConUnivTyVars dc) (G.dataConOrigResTy dc)
                functional = rFun "later" (ofType G.intTy) concrete
            assertBool "specialized Word8 schema retained in generic constructor" (deferredConstructorEquation concrete equation)
            assertBool "uniform owned schema unnecessarily deferred" (not (deferredConstructorEquation generic equation))
            assertBool "functional schema silently migrated" (not (deferredConstructorEquation functional equation))
            assertBool "incompatible original observation silently deferred" (not (deferredConstructorEquation concrete equation{dsort = Just (ofType (list G.boolTy))}))
            let declaration = M (name dc) concrete [equation] MsMeasure []
                original = mkMSpec' [declaration]
                projected = constructorEquationSchemas original
            assertBool "specialized eager equation retained" (null (concat (HM.elems (ctorMap projected))))
            measMap projected @?= measMap original
            imeas projected @?= imeas original
        , testCase "schema projection precedes abstract input and observation erasure" $ do
            let dc = G.nilDataCon
                carrier = G.mkTyConApp G.listTyCon [G.word8Ty]
                abstract = mapRBase (const (MkUReft mempty (Pr [PV "unsupported" NoReft []]))) (ofType carrier :: SpecType)
                signature = rFun "input" abstract (ofType G.boolTy)
                equation = Def (name dc) dc Nothing [] (P F.PTrue)
                declaration = M (name dc) signature [equation] MsMeasure []
                original = mkMSpec' [declaration]
                projected = constructorEquationSchemas original
            ctorMap projected @?= ctorMap original
            measMap projected @?= measMap original
            assertBool "abstract observation silently lost" (not (deferredConstructorEquation (measureSignature (ofType carrier)) equation{dsort = Just abstract}))
        , testCase "hidden callback and unsupported constructor transports are not deferred" $ do
            program <- compileToCore "ScopedEquationFields" scopedEquationFields
            hidden <- fixtureConstructor program "selectHidden"
            wrapped <- fixtureConstructor program "selectWrapped"
            indexed <- fixtureConstructor program "selectIndexed"
            let callback = G.mkVisFunTyMany G.intTy G.intTy
                carrier = G.mkTyConApp (G.dataConTyCon hidden) [G.word8Ty]
                actual = G.mkVisFunTyMany callback carrier
                equation = Def (name hidden) hidden Nothing [("callback", Nothing)] (P F.PTrue)
            assertBool "hidden callback bypassed latent source field membership" (isNothing (instantiateConstructorEquation (measureSignature (ofType carrier)) actual equation))
            assertBool "hidden callback schema silently deferred" (not (deferredConstructorEquation (measureSignature (ofType carrier)) equation))
            let wrappedCarrier = G.mkTyConApp (G.dataConTyCon wrapped) [G.word8Ty]
                wrappedEquation = Def (name wrapped) wrapped Nothing [("field", Nothing)] (P F.PTrue)
                indexedCarrier = G.mkTyConApp (G.dataConTyCon indexed) [G.mkTyConApp G.maybeTyCon [G.word8Ty]]
                indexedEquation = Def (name indexed) indexed Nothing [("field", Nothing)] (P F.PTrue)
            assertBool "nonidentical transport control has no lawful source instance" (isJust (instantiateConstructorEquation (measureSignature (ofType indexedCarrier)) (G.mkVisFunTyMany G.intTy indexedCarrier) indexedEquation))
            assertBool "newtype cast schema lost without a replacement hook" (not (deferredConstructorEquation (measureSignature (ofType wrappedCarrier)) wrappedEquation))
            assertBool "source/worker nonidentical schema lost without a replacement hook" (not (deferredConstructorEquation (measureSignature (ofType indexedCarrier)) indexedEquation))
        , testCase "unannotated callback fields cannot activate scoped constructor equations" $ do
            let dc = G.justDataCon
                callback = G.mkVisFunTyMany G.intTy G.intTy
                carrier = G.mkTyConApp G.maybeTyCon [callback]
                actual = G.mkVisFunTyMany callback carrier
                equation = Def (name dc) dc Nothing [("callback", Nothing)] (P F.PTrue)
            assertBool "latent callback domain ignored" (isNothing (instantiateConstructorEquation (measureSignature (ofType carrier)) actual equation))
            assertBool "unsupported callback equation silently migrated" (not (deferredConstructorEquation (measureSignature (ofType carrier)) equation))
        , testCase "scoped specialized equation retains observed refinements as premises" $ do
            let dc = G.consDataCon
                list = G.mkTyConApp G.listTyCon . (: [])
                carrier = list G.word8Ty
                actual = G.mkVisFunTyMany G.word8Ty (G.mkVisFunTyMany carrier carrier)
                domain = F.PAtom F.Eq (F.EVar "input") (F.EVar "allowed")
                old = F.PAtom F.Eq (F.EVar "original") (F.EVar "observed")
                input = strengthen (ofType carrier) (F.Reft ("input", domain))
                observed = strengthen (ofType carrier) (F.Reft ("original", old))
                equation = Def (name dc) dc (Just observed) [("head", Just (ofType G.word8Ty)), ("tail", Just (ofType carrier))] (E (F.EVar "head"))
                self = F.eApps (F.EVar (lhNameToResolvedSymbol (F.val (name dc)))) [F.EVar "original"]
                expected = mapRBase (const (F.Reft ("original", F.PAtom F.Eq self (F.EIte (F.pAnd [F.PAtom F.Eq (F.EVar "original") (F.EVar "allowed"), old]) (F.EVar "head") self)))) (ofType carrier)
            case instantiateConstructorEquation (measureSignatureFor G.word8Ty input) actual equation of
                Nothing -> assertFailure "specialized list equation rejected"
                Just result -> do
                    assertBool "actual carrier changed" (G.eqType (toType False result) carrier)
                    stripRTypeBase result @?= stripRTypeBase expected
                    checkEquationSort dc (measureSignatureFor G.word8Ty input) result [("head", G.word8Ty), ("tail", carrier), ("allowed", carrier), ("observed", carrier)]
                    dsort equation @?= Just observed
        , testCase "scoped generic actual coordinate cannot activate a specialized equation" $ do
            let dc = G.nilDataCon
                list ty = G.mkTyConApp G.listTyCon [ty]
                equation = Def (name dc) dc Nothing [] (P F.PTrue)
            assertBool "concrete Word8 carrier rejected" (isJust (instantiateConstructorEquation (measureSignature (ofType (list G.word8Ty))) (list G.word8Ty) equation))
            assertBool "Word8 equation admitted at Int carrier with the same numeric SMT sort" (isNothing (instantiateConstructorEquation (measureSignature (ofType (list G.word8Ty))) (list G.intTy) equation))
            assertBool "same-Unique rigid constructor variable specialized to Word8" (isNothing (instantiateConstructorEquation (measureSignature (ofType (list G.word8Ty))) (G.dataConOrigResTy dc) equation))
            assertBool "same-Unique universally owned measure variable was not instantiated independently" (isJust (instantiateConstructorEquation (universal (G.dataConUnivTyVars dc) (G.dataConOrigResTy dc)) (G.dataConOrigResTy dc) equation))
        , testCase "scoped nominal and original field mismatches cannot be reconciled independently" $ do
            let dc = G.consDataCon
                list ty = G.mkTyConApp G.listTyCon [ty]
                actual = G.mkVisFunTyMany G.intTy (G.mkVisFunTyMany (list G.intTy) (list G.intTy))
                incoherent = G.mkVisFunTyMany G.boolTy (G.mkVisFunTyMany (list G.intTy) (list G.intTy))
                equation = Def (name dc) dc Nothing [("head", Just (ofType G.boolTy)), ("tail", Just (ofType (list G.intTy)))] (P F.PTrue)
            assertBool "Bool input admitted at Int carrier" (isNothing (instantiateConstructorEquation (measureSignature (ofType (list G.boolTy))) actual equation{binds = [("head", Nothing), ("tail", Nothing)]}))
            assertBool "Bool field admitted at Int carrier" (isNothing (instantiateConstructorEquation (measureSignature (ofType (list G.intTy))) actual equation))
            assertBool "actual Bool field admitted at Int receiver without authored field annotations" (isNothing (instantiateConstructorEquation (measureSignature (ofType (list G.intTy))) incoherent equation{binds = [("head", Nothing), ("tail", Nothing)]}))
        , testCase "scoped repeated coordinates retain one rigid instantiation" $ do
            let dc = G.tupleDataCon G.Boxed 2
                pair left right = G.mkTyConApp (G.tupleTyCon G.Boxed 2) [left, right]
                actual = G.mkVisFunTyMany G.intTy (G.mkVisFunTyMany G.boolTy (pair G.intTy G.boolTy))
                equation = Def (name dc) dc Nothing [("left", Nothing), ("right", Nothing)] (P F.PTrue)
            assertBool "repeated Int indices admitted at Int/Bool carrier" (isNothing (instantiateConstructorEquation (measureSignature (ofType (pair G.intTy G.intTy))) actual equation))
        , testCase "ordinary measure instantiation is alpha-independent and unowned annotations stay rigid" $ do
            let dc = G.nilDataCon
                variables = G.dataConUnivTyVars dc
                original = G.dataConOrigResTy dc
                (rename, renamedVariables) = G.substTyVarBndrs (G.mkEmptySubst (G.mkInScopeSet (G.mkVarSet variables))) variables
                renamed = G.substTy rename original
                equation carrier = Def (name dc) dc (Just (ofType carrier)) [] (P F.PTrue)
                first = instantiateConstructorEquation (universal variables original) original (equation original)
                second = instantiateConstructorEquation (universal renamedVariables renamed) original (equation renamed)
                concrete = G.mkTyConApp G.listTyCon [G.word8Ty]
            assertBool "owned original annotation rejected" (isJust first)
            fmap stripRTypeBase first @?= fmap stripRTypeBase second
            assertBool "unowned annotation variable was specialized" (isNothing (instantiateConstructorEquation (universal variables original) concrete (equation renamed)))
        , testCase "nested input and observation domains are refused rather than dropped" $ do
            let dc = G.nilDataCon
                carrier = G.mkTyConApp G.listTyCon [G.word8Ty]
                narrowed = mapRBase (const F.trueReft) (fmap (const (F.Reft (F.vv_, F.PFalse))) (ofType carrier :: RRType F.Reft))
                equation = Def (name dc) dc Nothing [] (P F.PTrue)
            assertBool "nested input membership was ignored" (isNothing (instantiateConstructorEquation (measureSignature narrowed) carrier equation))
            assertBool "nested observed result membership was ignored" (isNothing (instantiateConstructorEquation (measureSignature (ofType carrier)) carrier equation{dsort = Just narrowed}))
            let secondInput = strengthen (ofType G.intTy) (MkUReft (F.Reft (F.vv_, F.PFalse)) mempty)
                multiple = rFun "source" (ofType carrier) (rFun "later" secondInput (ofType G.boolTy))
            assertBool "later runtime input membership was ignored" (isNothing (instantiateConstructorEquation multiple carrier equation))
        , testCase "false observed result and field predicates are conditional premises" $ do
            let dc = G.consDataCon
                carrier = G.mkTyConApp G.listTyCon [G.intTy]
                actual = G.mkVisFunTyMany G.intTy (G.mkVisFunTyMany carrier carrier)
                equation = Def (name dc) dc Nothing [("head", Nothing), ("tail", Nothing)] (E (F.EVar "head"))
                falseAt :: G.Type -> RRType F.Reft
                falseAt ty = strengthen (ofType ty) (F.Reft ("receiver", F.PFalse))
                checkPremise observed = case instantiateConstructorEquation (measureSignatureFor G.intTy (ofType carrier)) actual observed of
                    Nothing -> assertFailure "scalar false observation lost rather than guarded"
                    Just result -> case stripRTypeBase result of
                        Just (F.Reft (binder, predicate)) -> do
                            let self = F.eApps (F.EVar (lhNameToResolvedSymbol (F.val (name dc)))) [F.EVar binder]
                            predicate @?= F.PAtom F.Eq self (F.EIte F.PFalse (F.EVar "head") self)
                            checkEquationSort dc (measureSignatureFor G.intTy (ofType carrier)) result [("head", G.intTy), ("tail", carrier)]
                        Nothing -> assertFailure "receiver refinement missing"
            checkPremise equation{dsort = Just (falseAt carrier)}
            checkPremise equation{binds = [("head", Just (falseAt G.intTy)), ("tail", Nothing)]}
        , testCase "receiver binder cannot capture an original field named v" $ do
            let dc = G.consDataCon
                carrier = G.mkTyConApp G.listTyCon [G.intTy]
                actual = G.mkVisFunTyMany G.intTy (G.mkVisFunTyMany carrier carrier)
                observed = strengthen (ofType carrier) (F.Reft ("v", F.PAtom F.Eq (F.EVar "v") (F.EVar "observed")))
                field = strengthen (ofType G.intTy) (F.Reft ("field", F.PAtom F.Gt (F.EVar "field") (F.expr (0 :: Integer))))
                equation = Def (name dc) dc (Just observed) [("v", Just field), ("tail", Nothing)] (E (F.EVar "v"))
            case instantiateConstructorEquation (measureSignatureFor G.intTy (ofType carrier)) actual equation of
                Nothing -> assertFailure "capture-safe scalar premises rejected"
                Just result -> case stripRTypeBase result of
                    Just (F.Reft (binder, predicate)) -> do
                        assertBool "receiver captured the free field v" (binder /= "v")
                        let self = F.eApps (F.EVar (lhNameToResolvedSymbol (F.val (name dc)))) [F.EVar binder]
                            condition = F.pAnd [F.PAtom F.Eq (F.EVar binder) (F.EVar "observed"), F.PAtom F.Gt (F.EVar "v") (F.expr (0 :: Integer))]
                        predicate @?= F.PAtom F.Eq self (F.EIte condition (F.EVar "v") self)
                        checkEquationSort dc (measureSignatureFor G.intTy (ofType carrier)) result [("v", G.intTy), ("tail", carrier), ("observed", carrier)]
                    Nothing -> assertFailure "receiver refinement missing"
        , testCase "requested measure output refinement supplies no equation premise" $ do
            let dc = G.nilDataCon
                carrier = G.mkTyConApp G.listTyCon [G.intTy]
                equation = Def (name dc) dc Nothing [] (P F.PTrue)
                ordinary = measureSignature (ofType carrier)
                falseOutput = rFun "argument" (ofType carrier) (strengthen (ofType G.boolTy) (MkUReft (F.Reft (F.vv_, F.PFalse)) mempty))
            fmap stripRTypeBase (instantiateConstructorEquation ordinary carrier equation) @?= fmap stripRTypeBase (instantiateConstructorEquation falseOutput carrier equation)
        , testCase "phantom result and declared input share one substitution" $ do
            let dc = G.nilDataCon
                target = G.varType (G.dataConWorkId dc)
                input t = G.mkTyConApp G.listTyCon [t]
                observed = Def (name dc) dc (Just (ofType (input G.intTy))) [] (P F.PTrue)
            assertBool "original observation rejected" (definitionFits target observed)
            assertBool "declared input alone rejected" (definitionFitsInput (input G.boolTy) target observed{dsort = Nothing})
            assertBool "incompatible phantom substitutions admitted" (not (definitionFitsInput (input G.boolTy) target observed))
        , testCase "original typed fields retain joint declared-input correlations" $ do
            let dc = G.tupleDataCon G.Boxed 2
                target = G.varType (G.dataConWorkId dc)
                input t = G.mkTyConApp (G.tupleTyCon G.Boxed 2) [G.intTy, t]
                observed = Def (name dc) dc Nothing [("left", Just (ofType G.intTy)), ("right", Just (ofType G.intTy))] (P F.PTrue)
            assertBool "matching original fields rejected" (definitionFitsInput (input G.intTy) target observed)
            assertBool "original field observation overwritten" (not (definitionFitsInput (input G.boolTy) target observed))
        , testCase "untyped equations still require the declared nominal input" $ do
            let dc = G.nilDataCon
                target = G.varType (G.dataConWorkId dc)
                observed = Def (name dc) dc Nothing [] (P F.PTrue)
                wrong = G.mkTyConApp (G.tupleTyCon G.Boxed 2) [G.intTy, G.intTy]
            assertBool "unobserved constructor rejected" (definitionFits target observed)
            assertBool "wrong nominal input admitted by arity alone" (not (definitionFitsInput wrong target observed))
        , testCase "typed result and every original field observation remain joint" $ do
            let dc = G.tupleDataCon G.Boxed 2
                target = G.varType (G.dataConWorkId dc)
                pair t = G.mkTyConApp (G.tupleTyCon G.Boxed 2) [t, t]
                observed = Def (name dc) dc (Just (ofType (pair G.boolTy))) [("left", Just (ofType G.intTy)), ("right", Just (ofType G.intTy))] (P F.PTrue)
            assertBool "original fields/result conflict accepted" (not (definitionFits target observed))
            assertBool "declared input overwrote original typed result" (not (definitionFitsInput (pair G.intTy) target observed))
        , testCase "function-result measure uses its first declared input" $ do
            let dc = G.tupleDataCon G.Boxed 2
                input = G.mkTyConApp (G.tupleTyCon G.Boxed 2) [G.intTy, G.intTy]
                signature = G.mkVisFunTyMany input (G.mkVisFunTyMany G.intTy G.intTy)
                equation = Def (name dc) dc Nothing [("left", Nothing), ("right", Nothing)] (E (F.ELam ("argument", F.intSort) (F.EVar "argument")))
                declaration = M (name dc) (ofType signature) [equation] MsMeasure []
            case check declaration of
                Right () -> pure ()
                Left errors -> assertFailure (F.showpp (allErrors errors))
        , testCase "missing declared input returns a formation diagnostic" $ do
            let dc = G.nilDataCon
                equation = Def (name dc) dc Nothing [] (E (F.ECon (F.I 0)))
                declaration = M (name dc) (ofType G.intTy) [equation] MsMeasure []
            case check declaration of
                Left errors -> assertBool "missing input diagnostic lost" ("measure equation has no declared input" `isInfixOf` F.showpp (allErrors errors))
                Right () -> assertFailure "nullary declaration admitted a constructor equation"
        , testCase "deferred equation metadata cannot erase authored constructor formation" $ do
            let empty = emptyTarget defConfig
                spec = giSpec empty
                dat = gsData spec
                names = gsName spec
                owner = G.dataConWorkId G.trueDataCon
                predicate = F.PAtom F.Eq (F.EVar F.vv_) (F.ECon (F.I 1))
                malformed = fmap (const (MkUReft (F.Reft (F.vv_, predicate)) mempty)) (ofType G.boolTy :: SpecType)
                wildcard = [(["field"], F.EVar "field")]
                target = spec{gsData = dat{gsCtors = [(owner, F.dummyLoc malformed)], gsUnsorted = wildcard}, gsName = names{gsTcEmbeds = F.tceInsert G.boolTyCon F.boolSort F.NoArgs mempty}}
                run templates = checkTargetSpec templates [] [mempty] (giSrc empty) mempty [] target
            case run wildcard of
                Right () -> pure ()
                Left errors -> assertFailure ("collision control did not erase the predicate: " ++ F.showpp (allErrors errors))
            case run [] of
                Left _ -> pure ()
                Right () -> assertFailure "runtime equation metadata erased authored constructor formation"
        , testCase "same-owner authored and lifted names reject before projection" $ do
            let dc = G.nilDataCon
                signature = G.mkVisFunTyMany (G.mkTyConApp G.listTyCon [G.intTy]) G.boolTy
                equation = Def (name dc) dc Nothing [] (P F.PTrue)
                declaration = M (name dc) (ofType signature :: SpecType) [equation] MsMeasure []
                lifted = declaration{msKind = MsLifted}
            outcome <- Ex.try (Ex.evaluate (length (checkDuplicateMeasure [declaration, lifted]))) :: IO (Either UserError Int)
            case outcome of
                Left ErrDupMeas{} -> pure ()
                Left failure -> assertFailure ("wrong duplicate diagnostic: " ++ F.showpp failure)
                Right _ -> assertFailure "same-owner authored contribution silently lost to lifted projection"
        , testCase "original typing observations do not replace canonical uniqueness" $ do
            let dc = G.nilDataCon
                list t = G.mkTyConApp G.listTyCon [t]
                signature = G.mkVisFunTyMany (list G.boolTy) G.boolTy
                equation = Def (name dc) dc Nothing [] (P F.PTrue)
                canonical = M (name dc) (ofType signature :: SpecType) [equation] MsLifted []
                incompatible = canonical{msEqns = [equation{dsort = Just (ofType (list G.intTy))}]}
            case checkOriginals [canonical, canonical] canonical of
                Right () -> pure ()
                Left errors -> assertFailure ("repeated canonical observation became a duplicate declaration: " ++ F.showpp (allErrors errors))
            case checkOriginals [incompatible] canonical of
                Left errors -> assertBool "original correlation diagnostic lost" ("measure fields disagree" `isInfixOf` F.showpp (allErrors errors))
                Right () -> assertFailure "canonical winning metadata erased an incompatible original observation"
        ]
  where
    measureSignature :: RRType F.Reft -> SpecType
    measureSignature = measureSignatureFor G.boolTy
    measureSignatureFor :: G.Type -> RRType F.Reft -> SpecType
    measureSignatureFor result input = rFun "argument" (fmap (\reft -> MkUReft reft mempty) input) (ofType result)
    universal :: [G.TyVar] -> G.Type -> SpecType
    universal variables input = foldr (\variable rest -> RAllT (makeRTVar (rTyVar variable)) rest mempty) (measureSignature (ofType input)) variables
    name dc = F.dummyLoc (makeGHCLHNameFromId (G.dataConWorkId dc))
    checkEquationSort :: G.DataCon -> SpecType -> RRType F.Reft -> [(F.Symbol, G.Type)] -> Assertion
    checkEquationSort dc declaration result coordinates = case stripRTypeBase result of
        Nothing -> assertFailure "receiver refinement missing"
        Just (F.Reft (binder, predicate)) -> do
            let embeddings = F.tceInsert G.word8TyCon F.intSort F.NoArgs (F.tceInsert G.intTyCon F.intSort F.NoArgs (F.tceInsert G.boolTyCon F.boolSort F.NoArgs mempty))
                environment =
                    F.fromListSEnv $
                        [(binder, rTypeSort embeddings result), (lhNameToResolvedSymbol (F.val (name dc)), rTypeSort embeddings declaration)]
                            ++ [(coordinate, rTypeSort embeddings (ofType carrier :: SpecType)) | (coordinate, carrier) <- coordinates]
            SortCheck.checkSortExpr Nothing F.dummySpan environment predicate @?= Just F.boolSort
    check = checkOriginals []
    checkOriginals originals declaration =
        let empty = emptyTarget defConfig
            spec = giSpec empty
            names = gsName spec
            embeds = F.tceInsert G.intTyCon F.intSort F.NoArgs (F.tceInsert G.boolTyCon F.boolSort F.NoArgs mempty)
         in checkTargetSpec [] originals [mempty] (giSrc empty) mempty [] spec{gsData = (gsData spec){gsMeasures = [declaration]}, gsName = names{gsTcEmbeds = embeds}}
