{-# LANGUAGE OverloadedStrings #-}

module LogicSupportTests (tests) where

import Control.Exception (throw)
import Data.String (fromString)
import qualified Language.Fixpoint.Types as F
import qualified Language.Haskell.Liquid.Transforms.CoreToLogic as Logic
import Language.Haskell.Liquid.Types.Errors
import Language.Haskell.Liquid.Types.RType
import Language.Haskell.Liquid.Types.RTypeOp
import Language.Haskell.Liquid.Types.RefType
import Language.Haskell.Liquid.Types.Types
import Language.Haskell.Liquid.UX.CmdLine (defConfig)
import qualified Liquid.GHC.API as G
import Test.Tasty
import Test.Tasty.HUnit

tests :: (String -> String -> IO G.CoreProgram) -> TestTree
tests compileToCore = withResource prepare (const (pure ())) $ \fixture ->
    testGroup
        "typed logical support"
        [ testCase "actual source owner and established declaration sort" $ do
            (owner, _, _) <- fixture
            let (meaning, support) = interpret mempty (G.Var owner)
            meaning @?= F.EVar (F.symbol owner)
            map fst support @?= [owner]
            map snd support @?= [rTypeSort mempty (classRFInfoType True (ofType (G.varType owner) :: SpecType))]
        , testCase "lambda ownership does not become free support" $ do
            (_, body, _) <- fixture
            let (meaning, support) = interpret mempty body
            assertBool "source lambda meaning lost" (case meaning of F.ELam{} -> True; _ -> False)
            retainLogicSupport (F.syms meaning) support @?= []
        , testCase "actual alias disappears but its source dependency remains" $ do
            (owner, G.Lam argument _, _) <- fixture
            let alias = G.setVarType argument (G.varType owner)
                expression = G.Let (G.NonRec alias (G.Var owner)) (G.Var alias)
                (meaning, support) = interpret mempty expression
            meaning @?= F.EVar (F.symbol owner)
            map fst (retainLogicSupport (F.syms meaning) support) @?= [owner]
        , testCase "unused support does not force its embedding" $ do
            (owner, _, _) <- fixture
            let (meaning, _) = interpret (error "support-only embedding forced") (G.Var owner)
            meaning @?= F.EVar (F.symbol owner)
        , testCase "synonym, equality evidence and method dictionary retain declaration schemas" $ do
            (_, _, program) <- fixture
            mapM_ (checkOwner program) ["aliased", "equality", "method"]
        ]
  where
    prepare = do
        program <- compileToCore "LogicalSupport" "{-# LANGUAGE GADTs #-}\nmodule LogicalSupport where\nidentity :: Int -> Int\nidentity x = x\ntype Alias = Int\naliased :: Alias -> Alias\naliased x = x\nequality :: (a ~ b) => a -> b\nequality x = x\nclass C a where observe :: a -> Bool\nmethod :: C a => a -> Bool\nmethod = observe\n"
        case [(owner, body) | (owner, body) <- G.flattenBinds program, G.getOccString owner == "identity"] of
            [(owner, body)] -> pure (owner, body, program)
            _ -> fail "missing actual source identity"
    checkOwner program name = case [owner | (owner, _) <- G.flattenBinds program, G.getOccString owner == name] of
        [owner] -> do
            let (meaning, support) = interpret mempty (G.Var owner)
            meaning @?= F.EVar (F.symbol owner)
            map fst support @?= [owner]
            map snd support @?= [rTypeSort mempty (classRFInfoType True (ofType (G.varType owner) :: SpecType))]
        _ -> assertFailure ("missing actual source owner " ++ name)

interpret :: F.TCEmb G.TyCon -> G.CoreExpr -> (F.Expr, LogicSupport)
interpret embeddings expression =
    either throw id $
        Logic.runToLogic
            mempty
            embeddings
            mempty
            mempty
            defConfig
            (\message -> ErrOther G.noSrcSpan (fromString message))
            (Logic.coreToLogic expression)
