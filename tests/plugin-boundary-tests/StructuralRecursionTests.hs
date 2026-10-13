module StructuralRecursionTests (tests) where

import CompilerFixture
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase)

tests :: (FilePath -> IO FilePath) -> IO Compiler -> Optimization -> TestTree
tests fixture compiler optimization =
    testGroup
        "structurally checked result contracts"
        [ testCase name $ withSystemTempDirectory "lh-structural-result" $ \directory -> do
            tool <- compiler
            copyFixture fixture ("plugin-boundary-tests/fixtures/termination" </> name ++ ".hs") directory name
            _ <- compile tool Strict optimization ObjectCode directory name [] [] expected
            pure ()
        | (name, expected) <-
            [ ("StructuralReflectedGood", Safe)
            , ("StructuralReflectedWrongBase", UnsafeAt [6])
            , ("StructuralMixedFailure", UnsafeAt [10])
            , ("StructuralMixedSkippedFiniteFalse", UnsafeAt [6, 11])
            , ("StructuralExpectedReuse", UnsafeAt [3, 11])
            , ("StructuralFunctionTopFalse", UnsafeAt [5])
            , ("StructuralLocalWrongBase", UnsafeAt [9])
            , ("StructuralMeasureWrongBase", UnsafeAt [6])
            ]
        ]
