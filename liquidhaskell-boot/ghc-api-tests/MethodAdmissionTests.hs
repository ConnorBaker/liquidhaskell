module MethodAdmissionTests (tests) where

import qualified Data.HashSet as S
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as FC
import Language.Haskell.Liquid.Constraint.Publication (publicationAdmissible)
import Language.Haskell.Liquid.Liquid (checkTargetInfo)
import Language.Haskell.Liquid.Types.RType (RTypeBV (..))
import Language.Haskell.Liquid.Types.RefType (ofType, strengthen, uTop)
import Language.Haskell.Liquid.Types.Specs
import Language.Haskell.Liquid.Types.Types (MethodType (..), ModName (..), ModType (..), Output (..), hole)
import qualified Language.Haskell.Liquid.UX.CmdLine as CmdLine
import qualified Language.Haskell.Liquid.UX.Config as LH
import Liquid.GHC.API (mkModuleName)
import qualified Liquid.GHC.API as G
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))

tests :: (LH.Config -> TargetInfo) -> (String -> String -> IO G.CoreProgram) -> TestTree
tests emptyTarget compileToCore =
    testGroup
        "class method admission binders"
        [ testCase label $ do
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
                            signatures = (gsSig spec){gsTySigs = [(owner, F.dummyLoc supplied)], gsMethods = [(owner, MT (Just (F.dummyLoc supplied)) (Just (F.dummyLoc schema)))]}
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
