module WiredInTests (tests) where

import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Types.Names (selfSymbol)
import Language.Haskell.Liquid.WiredIn (wiredSortedSyms)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

tests :: TestTree
tests =
    testGroup
        "wired logical sorts"
        [ testCase "self binds its result type variable" $
            -- The FQ printer records binder count, not binder indices: comparing
            -- printed text would miss FAbs 1 (FVar 0), which leaves 0 free.
            lookup selfSymbol wiredSortedSyms @?= Just (F.FAbs 0 (F.FVar 0))
        ]
