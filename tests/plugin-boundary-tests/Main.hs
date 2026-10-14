module Main (main) where

import CompilerFixture (Optimization (..), configuredCompiler)
import qualified ConstructorTests
import qualified DictionaryMethodTests
import qualified EmbeddingSortTests
import qualified ImportedBodyTests
import qualified NativeJudgmentTests
import qualified OpaqueIdentityTests
import Paths_tests (getDataFileName)
import qualified PublicationTests
import qualified SourceImportTests
import qualified SourceJudgmentTests
import qualified StructuralRecursionTests
import Test.Tasty (defaultMain, testGroup, withResource)

main :: IO ()
main = defaultMain $
    withResource configuredCompiler (const (pure ())) $ \compiler ->
        testGroup
            "installed plugin boundaries"
            [ testGroup
                (show optimization)
                [ ConstructorTests.tests getDataFileName compiler optimization
                , DictionaryMethodTests.tests getDataFileName compiler optimization
                , EmbeddingSortTests.tests getDataFileName compiler optimization
                , ImportedBodyTests.tests getDataFileName compiler optimization
                , NativeJudgmentTests.tests compiler optimization
                , PublicationTests.tests getDataFileName compiler optimization
                , SourceJudgmentTests.tests getDataFileName compiler optimization
                , SourceImportTests.tests compiler optimization
                , StructuralRecursionTests.tests getDataFileName compiler optimization
                , OpaqueIdentityTests.tests compiler optimization
                ]
            | optimization <- [O0, O2]
            ]
