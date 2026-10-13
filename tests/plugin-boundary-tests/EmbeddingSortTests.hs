module EmbeddingSortTests (tests) where

import CompilerFixture
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase)

tests :: (FilePath -> IO FilePath) -> IO Compiler -> Optimization -> TestTree
tests fixture compiler optimization =
    testGroup
        "nominal applied embeddings"
        [ testCase "source carrier identity and distinct nominal domain" $
            withSystemTempDirectory "lh-embedding-sort" $ \directory -> do
                tool <- compiler
                let provider = directory </> "provider"
                    copy target name = copyFixture fixture ("plugin-boundary-tests/fixtures/embedding-sorts" </> name ++ ".hs") target name
                mapM_
                    ( \name -> do
                        copy provider name
                        _ <- compile tool Strict optimization ObjectCode provider name [] [] Safe
                        pure ()
                    )
                    ["NominalEvidence", "OtherEvidence"]
                mapM_
                    ( \(name, expected) -> do
                        let target = directory </> name
                        copy target name
                        _ <- compile tool Strict optimization ObjectCode target name [provider </> "objects"] [] expected
                        pure ()
                    )
                    [ ("ProvenanceEmbeddingGood", Safe)
                    , ("ProvenanceEmbeddingFalse", UnsafeAt [11])
                    , ("ProvenanceEmbeddingWrongType", FormationRefusal 10 "Cannot unify")
                    , ("ProvenanceEmbeddingPrimitive", Safe)
                    , ("SourceAliasEmbeddingGood", Safe)
                    , ("SourceAliasEmbeddingWrong", FormationRefusal 7 "A source type synonym embedding disagrees with its definition.")
                    ]
        ]
