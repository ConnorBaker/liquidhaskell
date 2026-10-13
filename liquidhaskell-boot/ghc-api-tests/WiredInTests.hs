module WiredInTests (tests) where

import Data.Maybe (isNothing)
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.GHC.PrimitiveContract (primitiveContract, wiredBoolean)
import Language.Haskell.Liquid.Types.Names (selfSymbol)
import Language.Haskell.Liquid.Types.RTypeOp (rTypeReft)
import Language.Haskell.Liquid.WiredIn (wiredSortedSyms)
import qualified Liquid.GHC.API as G
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))

tests :: TestTree
tests =
    testGroup
        "wired logical sorts"
        [ testCase "self binds its result type variable" $
            -- The FQ printer records binder count, not binder indices: comparing
            -- printed text would miss FAbs 1 (FVar 0), which leaves 0 free.
            lookup selfSymbol wiredSortedSyms @?= Just (F.FAbs 0 (F.FVar 0))
        , testCase "actual Boolean constructors have their logical truth values" $
            mapM_ constructorMeaning [(G.trueDataConId, id), (G.falseDataConId, F.PNot)]
        , testCase "an alternate Boolean embedding is not the built-in logical Boolean" $
            assertBool "numeric embedding borrowed Boolean semantics" $
                isNothing $
                    primitiveContract Nothing (F.tceInsert G.boolTyCon F.FInt F.NoArgs mempty) [] (G.Var G.trueDataConId)
        , testCase "a same-spelled different native identifier is not wired True" $
            assertBool "occurrence spelling licensed a constructor fact" $
                isNothing $
                    primitiveContract Nothing booleanEmbedding [] (G.Var $ G.setVarUnique G.trueDataConId $ G.mkUnique 'X' 987654)
        ]
  where
    booleanEmbedding = F.tceInsert G.boolTyCon F.boolSort F.NoArgs mempty
    constructorMeaning (constructor, proposition) = case primitiveContract Nothing booleanEmbedding [] (G.Var constructor) of
        Just (Right ty) -> do
            wiredBoolean booleanEmbedding (G.Var constructor) @?= Just (if constructor == G.trueDataConId then F.PTrue else F.PFalse)
            let F.Reft (root, predicate) = rTypeReft ty
            predicate @?= proposition (F.EVar root)
        _ -> assertFailure "the actual native Boolean constructor lost its contract"
