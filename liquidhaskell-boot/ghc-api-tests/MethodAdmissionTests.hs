module MethodAdmissionTests (tests) where

import Control.Monad.State (runState)
import qualified Data.HashSet as S
import qualified DefaultSchemaSharingTests
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as FC
import Language.Haskell.Liquid.Bare.Class (instanceDictionaryOwners)
import Language.Haskell.Liquid.Constraint.Env (lookupREnv)
import Language.Haskell.Liquid.Constraint.Generate (ConstraintObligations (..), generateConstraints)
import Language.Haskell.Liquid.Constraint.Init (initCGI, initEnv)
import Language.Haskell.Liquid.Constraint.Publication (publicationAdmissible)
import qualified Language.Haskell.Liquid.Constraint.Types as CG
import Language.Haskell.Liquid.Liquid (checkTargetInfo)
import Language.Haskell.Liquid.Types.RType (RTypeBV (..))
import Language.Haskell.Liquid.Types.RTypeOp (rTypeReft)
import Language.Haskell.Liquid.Types.RefType (ofType, strengthen, uTop)
import Language.Haskell.Liquid.Types.Specs
import Language.Haskell.Liquid.Types.Types (MethodType (..), ModName (..), ModType (..), Output (..), hole, logicalSpecType)
import qualified Language.Haskell.Liquid.UX.CmdLine as CmdLine
import qualified Language.Haskell.Liquid.UX.Config as LH
import Liquid.GHC.API (mkModuleName)
import qualified Liquid.GHC.API as G
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

tests :: (LH.Config -> TargetInfo) -> (String -> String -> IO G.CoreProgram) -> TestTree
tests emptyTarget compileToCore =
    testGroup
        "class method admission binders"
        $ [obligationSelection emptyTarget compileToCore, inferredCallableObservation emptyTarget compileToCore, derivedInterfaceAuthority emptyTarget compileToCore, sharedMethodAuthority emptyTarget compileToCore]
            ++ [ testCase label $ do
                    program <- compileToCore moduleName (unlines ["module " ++ moduleName ++ " where", "checked :: Int -> Int", definition])
                    case [(owner, body) | (owner, body) <- G.flattenBinds program, G.getOccString owner == "checked"] of
                        [(owner, body)] -> case ofType (G.varType owner) of
                            RFun _ info domain result refinement -> do
                                let argument = F.symbol ("input" :: String)
                                    value = F.symbol ("VV" :: String)
                                    positive ty = strengthen ty (uTop (F.Reft (value, F.PAtom F.Gt (F.EVar value) (F.ECon (F.I 0)))))
                                    input = if accepts then positive domain else domain
                                    output = if accepts then F.EVar argument else F.ECon (F.I 0)
                                    resultPredicate = if inferResult then hole else F.PAtom F.Eq (F.EVar value) output
                                    supplied = RFun argument info input (strengthen result (uTop (F.Reft (value, resultPredicate)))) refinement
                                    schema = RFun binder info input (positive result) refinement
                                    empty = emptyTarget CmdLine.defConfig{LH.checkDerived = True, LH.checkRefinements = True, LH.totalHaskell = True, LH.noannotations = True, LH.smtsolver = Just FC.Z3}
                                    source = (giSrc empty){giTarget = moduleName ++ ".hs", giTargetMod = ModName Target (mkModuleName moduleName), giCbs = if localMethod then [G.NonRec owner body] else [], giDefVars = if localMethod then [owner] else [], giImpVars = if localMethod then [] else [owner]}
                                    spec = giSpec empty
                                    signatures = (gsSig spec){gsTySigs = [(owner, F.dummyLoc supplied)], gsMethods = [(owner, MT (Just (F.dummyLoc $ logicalSpecType supplied)) (Just (F.dummyLoc $ logicalSpecType schema)) Nothing)]}
                                    names = (gsName spec){gsTcEmbeds = F.tceFromList [(G.intTyCon, (F.FInt, F.NoArgs))]}
                                    targetInfo = empty{giSrc = source, giSpec = spec{gsSig = signatures, gsName = names}}
                                (checked, _, publication) <- checkTargetInfo targetInfo
                                case (accepts, o_result checked, publication) of
                                    (True, F.Safe _, Just evidence@(F.Safe _)) -> publicationAdmissible S.empty [] evidence @?= True
                                    (False, F.Unsafe _ _, Just evidence@(F.Unsafe _ _)) -> publicationAdmissible S.empty [] evidence @?= False
                                    _ -> assertFailure (label ++ ": " ++ show (o_result checked) ++ "; publication: " ++ show publication)
                            _ -> assertFailure "expected the actual Int method telescope"
                        _ -> assertFailure "expected one checked source owner"
               | (label, moduleName, binder, definition, accepts, localMethod, inferResult) <-
                    [ ("anonymous positive schema", "AnonymousPositiveMethod", F.dummySymbol, "checked x = x", True, True, False)
                    , ("named positive schema", "NamedPositiveMethod", F.symbol ("schemaInput" :: String), "checked x = x", True, True, False)
                    , ("zero result cannot satisfy a positive schema", "RejectedZeroMethod", F.dummySymbol, "checked _ = 0", False, True, False)
                    , ("compatible imported method has no local body", "ImportedPositiveMethod", F.dummySymbol, "checked x = x", True, False, False)
                    , ("incompatible imported method cannot publish", "ImportedZeroMethod", F.dummySymbol, "checked _ = 0", False, False, False)
                    , ("inferred positive result satisfies the schema", "InferredPositiveMethod", F.dummySymbol, "checked x = x", True, True, True)
                    , ("inferred zero result cannot satisfy a positive schema", "RejectedInferredZeroMethod", F.dummySymbol, "checked _ = 0", False, True, True)
                    ]
               ]

-- No checking declaration exists for the private helper. Its inferred output
-- remains a requested solver observation and a premise for the later body.
inferredCallableObservation :: (LH.Config -> TargetInfo) -> (String -> String -> IO G.CoreProgram) -> TestTree
inferredCallableObservation emptyTarget compileToCore =
    testGroup
        "private inferred callable observations"
        [ testCase label $ do
            program <-
                compileToCore name $
                    unlines
                        [ "module " ++ name ++ " (checked) where"
                        , "helper :: Int -> Int"
                        , "helper _ = " ++ show value
                        , "{-# NOINLINE helper #-}"
                        , "checked :: Int -> Int"
                        , "checked x = helper x"
                        ]
            let bodies = [(owner, body) | (owner, body) <- G.flattenBinds program, G.getOccString owner `elem` ["helper", "checked"]]
            case ([owner | (owner, _) <- bodies, G.getOccString owner == "checked"], [owner | (owner, _) <- bodies, G.getOccString owner == "helper"]) of
                ([owner], [helper]) -> case ofType (G.varType owner) of
                    RFun _ info domain result refinement -> do
                        let root = F.symbol ("VV" :: String)
                            input = F.symbol ("sourceInput" :: String)
                            predicates = F.PAtom F.Eq (F.EVar root) (F.ECon (F.I 0)) : [F.PAtom F.Eq (F.EVar root) (F.EApp (F.eVar helper) (F.EVar input)) | observeIdentity]
                            zero = strengthen result (uTop (F.Reft (root, F.pAnd predicates)))
                            declaration = RFun input info domain zero refinement
                            empty = emptyTarget CmdLine.defConfig{LH.checkDerived = True, LH.checkRefinements = True, LH.totalHaskell = True, LH.noannotations = True, LH.smtsolver = Just FC.Z3, LH.noslice = noSlice}
                            source = (giSrc empty){giTarget = name ++ ".hs", giTargetMod = ModName Target (mkModuleName name), giCbs = [G.NonRec identifier body | (identifier, body) <- bodies], giDefVars = map fst bodies}
                            spec = giSpec empty
                            -- The opaque/reflected Haskell scheme is an
                            -- interface cut, not an authored output claim.
                            signatures = (gsSig spec){gsTySigs = [(owner, F.dummyLoc declaration)], gsRefSigs = [(helper, F.dummyLoc (ofType (G.varType helper)))]}
                            names = (gsName spec){gsTcEmbeds = F.tceFromList [(G.intTyCon, (F.FInt, F.NoArgs))]}
                            target = empty{giSrc = source, giSpec = spec{gsSig = signatures, gsName = names}}
                        (output, _, _) <- checkTargetInfo target
                        case (accepts, o_result output) of
                            (True, F.Safe _) -> pure ()
                            (False, F.Unsafe _ _) -> pure ()
                            _ -> assertFailure (show (o_result output))
                    _ -> assertFailure "expected the checked source function"
                _ -> assertFailure "expected one checked source owner"
        | (label, name, value, accepts, noSlice, observeIdentity) <-
            [ ("inferred zero survives safety slicing and its weaker checking view", "PrivateZeroObservation", 0 :: Int, True, False, False)
            , ("inferred zero survives weaker checking with explicit noSlice", "PrivateZeroNoSliceObservation", 0, True, True, False)
            , ("inferred one does not acquire a zero postcondition", "PrivateOneObservation", 1, False, False, False)
            , ("source-call identity retains the independently proved zero result", "PrivateZeroIdentityObservation", 0, True, False, True)
            , ("source-call identity cannot replace an independently proved one result", "PrivateOneIdentityObservation", 1, False, False, True)
            ]
        ]

-- The same actual instance field is checked or trusted according to the
-- compiler's derived-owner inventory. Trust must not resurrect an erased
-- checking goal as evidence for contextual interface subsumption.
derivedInterfaceAuthority :: (LH.Config -> TargetInfo) -> (String -> String -> IO G.CoreProgram) -> TestTree
derivedInterfaceAuthority emptyTarget compileToCore =
    testGroup
        "derived interface authority"
        [ testCase label $ do
            program <- compileToCore "DerivedInterfaceAuthority" "module DerivedInterfaceAuthority where\nclass K a where selected :: a -> a\ninstance K Int where selected x = x\n"
            case [(dictionary, selector, owner, body) | (dictionary, _) <- G.flattenBinds program, G.isDFunId dictionary, Just fields <- [instanceDictionaryOwners program dictionary], (selector, owner) <- fields, Just body <- [lookup owner (G.flattenBinds program)]] of
                [(dictionary, selector, owner, body)] -> case ofType (G.varType owner) of
                    RFun binder info domain result refinement -> do
                        let root = F.symbol ("VV" :: String)
                            positive ty = strengthen ty (uTop (F.Reft (root, F.PAtom F.Gt (F.EVar root) (F.ECon (F.I 0)))))
                            target = RFun binder info (positive domain) (positive result) refinement
                            empty = emptyTarget CmdLine.defConfig{LH.checkDerived = checkBody, LH.checkRefinements = True, LH.totalHaskell = True, LH.noannotations = True, LH.smtsolver = Just FC.Z3}
                            source = (giSrc empty){giTarget = "DerivedInterfaceAuthority.hs", giTargetMod = ModName Target (mkModuleName "DerivedInterfaceAuthority"), giCbs = [G.NonRec owner body], giDefVars = [owner], giDerVars = S.singleton owner}
                            spec = giSpec empty
                            signatures = (gsSig spec){gsMethods = [(owner, MT (Just (F.dummyLoc $ logicalSpecType target)) (Just (F.dummyLoc $ logicalSpecType target)) (Just (dictionary, selector)))]}
                            names = (gsName spec){gsTcEmbeds = F.tceFromList [(G.intTyCon, (F.FInt, F.NoArgs))]}
                        (output, _, _) <- checkTargetInfo empty{giSrc = source, giSpec = spec{gsSig = signatures, gsName = names}}
                        case (checkBody, o_result output) of
                            (True, F.Safe _) -> pure ()
                            (False, F.Unsafe _ _) -> pure ()
                            _ -> assertFailure (show (o_result output))
                    _ -> assertFailure "expected the actual instance field telescope"
                _ -> assertFailure "expected one actual dictionary field owner"
        | (label, checkBody) <- [("checked derived body establishes its interface", True), ("trusted derived body cannot resurrect the erased interface", False)]
        ]

-- Desugaring shares the actual implementation Id across these two dictionary
-- fields. Each authored private claim is an obligation, even when the checking
-- environment selects a different row for that same source owner.
sharedMethodAuthority :: (LH.Config -> TargetInfo) -> (String -> String -> IO G.CoreProgram) -> TestTree
sharedMethodAuthority emptyTarget compileToCore =
    testGroup
        "shared method authority"
        [ testCase label $ do
            program <-
                compileToCore "SharedMethodAuthority" $
                    unlines
                        [ "{-# LANGUAGE AllowAmbiguousTypes #-}"
                        , "module SharedMethodAuthority where"
                        , "class Marker a where selected :: Int"
                        , "shared :: Int"
                        , "shared = 0"
                        , "instance Marker Int where selected = shared"
                        , "instance Marker Bool where selected = shared"
                        ]
            case [(owner, body) | (owner, body) <- G.flattenBinds program, G.getOccString owner == "shared"] of
                [(owner, body)] -> do
                    let origins = [(dictionary, selector) | (dictionary, _) <- G.flattenBinds program, G.isDFunId dictionary, Just fields <- [instanceDictionaryOwners program dictionary], (selector, implementation) <- fields, implementation == owner]
                    length origins @?= 2
                    let plain = ofType (G.varType owner)
                        root = F.symbol ("VV" :: String)
                        zero = strengthen plain (uTop (F.Reft (root, F.PAtom F.Eq (F.EVar root) (F.ECon (F.I 0)))))
                        positive = strengthen plain (uTop (F.Reft (root, F.PAtom F.Gt (F.EVar root) (F.ECon (F.I 0)))))
                        rows = [(owner, MT (Just (F.dummyLoc $ logicalSpecType private)) (Just (F.dummyLoc $ logicalSpecType plain)) (Just origin)) | (origin, private) <- zip origins [if conflicting then positive else zero, zero]]
                        ordered = if reversed then reverse rows else rows
                        empty = emptyTarget CmdLine.defConfig{LH.checkDerived = True, LH.checkRefinements = True, LH.totalHaskell = True, LH.noannotations = True, LH.smtsolver = Just FC.Z3}
                        source = (giSrc empty){giTarget = "SharedMethodAuthority.hs", giTargetMod = ModName Target (mkModuleName "SharedMethodAuthority"), giCbs = [G.NonRec owner body], giDefVars = [owner]}
                        spec = giSpec empty
                        signatures = (gsSig spec){gsMethods = ordered}
                        names = (gsName spec){gsTcEmbeds = F.tceFromList [(G.intTyCon, (F.FInt, F.NoArgs))]}
                    (output, _, _) <- checkTargetInfo empty{giSrc = source, giSpec = spec{gsSig = signatures, gsName = names}}
                    case (conflicting, o_result output) of
                        (False, F.Safe _) -> pure ()
                        (True, F.Unsafe _ _) -> pure ()
                        _ -> assertFailure (show (o_result output))
                _ -> assertFailure "expected the actual shared source implementation"
        | (label, conflicting, reversed) <-
            [("every shared private claim is checked", True, False), ("conflicting claims reject in reversed catalog order", True, True), ("consistent shared claims admit both origins", False, False), ("consistent claims admit in reversed catalog order", False, True)]
        ]

obligationSelection :: (LH.Config -> TargetInfo) -> (String -> String -> IO G.CoreProgram) -> TestTree
obligationSelection emptyTarget compileToCore =
    testCase "method proof selection preserves its checking declaration catalog" $ do
        program <- compileToCore "MethodObligationSelection" "module MethodObligationSelection where\nselected :: Int -> Int\nselected x = x\n"
        case [owner | (owner, _) <- G.flattenBinds program, G.getOccString owner == "selected"] of
            [owner] -> case ofType (G.varType owner) of
                RFun binder info domain result refinement -> do
                    let value = F.symbol ("VV" :: String)
                        zero ty = strengthen ty (uTop (F.Reft (value, F.PAtom F.Eq (F.EVar value) (F.ECon (F.I 0)))))
                        positive ty = strengthen ty (uTop (F.Reft (value, F.PAtom F.Gt (F.EVar value) (F.ECon (F.I 0)))))
                        supplied = RFun binder info domain (zero result) refinement
                        schema = RFun binder info domain (positive result) refinement
                        empty = emptyTarget CmdLine.defConfig
                        spec = giSpec empty
                        methods = [(owner, MT (Just (F.dummyLoc $ logicalSpecType supplied)) (Just (F.dummyLoc $ logicalSpecType schema)) Nothing)]
                        target = empty{giSrc = (giSrc empty){giDefVars = [owner]}, giSpec = spec{gsSig = (gsSig spec){gsMethods = methods}}}
                        initialize = initCGI (LH.getConfig target) target
                        defaults = DefaultSchemaSharingTests.schemas target target
                        (_, without) = generateConstraints initialize defaults [] target (ConstraintObligations [] [] mempty [])
                        (_, with) = generateConstraints initialize defaults [] target (ConstraintObligations [] methods mempty [])
                        (environment, _) = runState (initEnv defaults [] target) (initialize target)
                    CG.fixCs without @?= []
                    assertBool "selected method lost its positive-result compatibility goal" $
                        any
                            (\constraint -> let F.RR _ (F.Reft (root, predicate)) = F.srhs constraint in F.PAtom F.Gt (F.EVar root) (F.ECon (F.I 0)) `elem` F.conjuncts predicate)
                            (CG.fixCs with)
                    case lookupREnv (F.symbol owner) (CG.grtys environment) of
                        Just (RFun _ _ _ callableResult _) -> do
                            let F.Reft (root, predicate) = rTypeReft callableResult
                            assertBool "proof selection erased the supplied method checking result" $
                                F.PAtom F.Eq (F.EVar root) (F.ECon (F.I 0)) `elem` F.conjuncts predicate
                        _ -> assertFailure "method disappeared from its checking declaration catalog"
                _ -> assertFailure "expected the actual Int method telescope"
            _ -> assertFailure "expected one selected source method"
