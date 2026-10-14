module ConstructorTests (tests) where

import CompilerFixture
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase)

tests :: (FilePath -> IO FilePath) -> IO Compiler -> Optimization -> TestTree
tests fixture compiler optimization =
    testGroup "constructor source correspondence" $
        [ testCase (polarity ++ "/" ++ name) $ withSystemTempDirectory "lh-constructor" $ \directory -> do
            tool <- compiler
            copyFixture fixture (polarity </> name ++ ".hs") directory name
            _ <- compile tool Strict optimization ObjectCode directory name [] [] expected
            pure ()
        | (polarity, name, expected) <- cases
        ]
            ++ [ testCase "published constructor library and independent clients" $
                    withSystemTempDirectory "lh-constructor-import" $ \directory -> do
                        tool <- compiler
                        let producer = directory </> "producer"
                            provider = "ConstructorSourcePublicationLib"
                        copyFixture fixture ("import/lib" </> provider ++ ".hs") producer provider
                        compiled <- compile tool Strict optimization ObjectCode producer provider [] [] Safe
                        assertPublication tool compiled True
                        mapM_
                            (client tool directory producer)
                            [("ConstructorSourcePublication", Safe), ("ConstructorSourcePublicationFalse", UnsafeAt [9])]
               ]
  where
    client tool directory producer (name, expected) = do
        let target = directory </> name
        copyFixture fixture ("import/client" </> name ++ ".hs") target name
        _ <- compile tool Strict optimization ObjectCode target name [producer </> "objects"] [] expected
        pure ()
    cases =
        [ ("pos", name, Safe)
        | name <-
            [ "ConstructorAnonymousFields"
            , "ConstructorBoxedSource"
            , "ConstructorExistentialWorker"
            , "ConstructorPolymorphicReflection"
            , "ConstructorWholeSource"
            , "InterleavedMethodEvidence"
            , "MeasureArgumentScrutinee"
            ]
        ]
            ++ [ ("measure/pos", "MeasureGadt", Safe)
               , ("plugin-boundary-tests/fixtures/constructor-correspondence", "MeasureGadtFalse", UnsafeAt [15])
               , ("neg", "ConstructorAnonymousFields", UnsafeAt [16])
               , ("neg", "ConstructorBoxedSource", UnsafeAt [21])
               , ("neg", "ConstructorExistentialWorker", UnsafeAt [12])
               , ("neg", "ConstructorPolymorphicReflection", UnsafeAt [16])
               , ("neg", "ConstructorWholeSource", UnsafeAt [14])
               , ("neg", "InterleavedMethodEvidence", UnsafeAt [28])
               , ("neg", "MeasureUnrelatedScrutinee", FormationRefusal 11 "Case scrutinee is not the selected measure argument")
               , ("plugin-boundary-tests/fixtures/projection-admission", "PartialProjectionGood", Safe)
               , ("plugin-boundary-tests/fixtures/projection-admission", "PartialProjectionFalse", UnsafeAt [21])
               , ("plugin-boundary-tests/fixtures/projection-admission", "ImportedProjectionGood", Safe)
               , ("plugin-boundary-tests/fixtures/projection-admission", "ImportedProjectionFalse", UnsafeAt [19])
               , ("plugin-boundary-tests/fixtures/measure-source-name", "MeasureSourceNameGood", Safe)
               , ("plugin-boundary-tests/fixtures/measure-source-name", "MeasureSourceNameFalse", UnsafeAt [15])
               ]
