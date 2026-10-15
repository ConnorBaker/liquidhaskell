module DictionaryMethodTests (tests) where

import CompilerFixture
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase)

-- A dictionary argument is checked by its fields at the instantiated class
-- arguments: a known instance by its method contracts, any other dictionary
-- by the class constructor's field variance.
tests :: (FilePath -> IO FilePath) -> IO Compiler -> Optimization -> TestTree
tests fixture compiler optimization =
    testGroup "dictionary method contracts" $
        [ testCase name $ withSystemTempDirectory "lh-dictionary" $ \directory -> do
            tool <- compiler
            copyFixture fixture (root </> name ++ ".hs") directory name
            _ <- compile tool Strict optimization ObjectCode directory name [] [] expected
            pure ()
        | (name, expected) <- cases
        ]
            ++ [ testCase ("lawless library instance / " ++ client) $
                    withSystemTempDirectory "lh-dictionary-import" $ \directory -> do
                        tool <- compiler
                        let producer = directory </> "producer"
                            target = directory </> client
                        copyFixture fixture (root </> "lib" </> library ++ ".hs") producer library
                        _ <- compile tool Strict optimization ObjectCode producer library [] [] Safe
                        copyFixture fixture (root </> "client" </> client ++ ".hs") target client
                        _ <- compile tool Strict optimization ObjectCode target client [producer </> "objects"] [] expected
                        pure ()
               | (library, client, expected) <- imported
               ]
  where
    root = "plugin-boundary-tests/fixtures/dictionary-methods"
    cases =
        [ ("SetUnionIntGood", Safe)
        , ("SetInsertIntGood", Safe)
        , ("OrdPolyIntGood", Safe)
        , ("SetUnionTextGood", Safe)
        , ("SetUnionTextFieldGood", Safe)
        , ("SetUnionTextVarianceGood", Safe)
        , ("PickContractGood", Safe)
        , ("SuperclassContractGood", Safe)
        , ("IntegralPolyIntGood", Safe)
        , ("NumPolyIntGood", Safe)
        , ("SelectorArithmeticGood", Safe)
        , ("SetUnionIntFalse", UnsafeAt [7])
        , ("SetIdIntFalse", UnsafeAt [7])
        , ("OrdPolyIntFalse", UnsafeAt [9])
        , ("SetUnionKeyFalse", UnsafeAt [13])
        , ("SetUnionTextMeasureGood", Safe)
        , ("PickContractFalse", UnsafeAt [18])
        , ("SuperclassFabFalse", UnsafeAt [34])
        , -- Incomplete but sound: derived methods have no contracts.
          ("SetUnionDerivedOrd", UnsafeAt [15])
        ]
    imported =
        [ ("OrdFabLib", "OrdFabUse", UnsafeAt [7])
        , ("PickFabLib", "PickFabUse", UnsafeAt [7])
        ]
