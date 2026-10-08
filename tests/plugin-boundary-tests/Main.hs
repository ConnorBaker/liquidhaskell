module Main (main) where

import CompilerFixture (Optimization (..), configuredCompiler)
import qualified ConstructorTests
import qualified ImportedBodyTests
import qualified OpaqueIdentityTests
import Paths_tests (getDataFileName)
import qualified PublicationTests
import qualified SourceJudgmentTests
import Test.Tasty (defaultMain, testGroup, withResource)

main :: IO ()
main = defaultMain $
    withResource configuredCompiler (const (pure ())) $ \compiler ->
        testGroup
            "installed plugin boundaries"
            [ testGroup
                (show optimization)
                [ ConstructorTests.tests getDataFileName compiler optimization
                , ImportedBodyTests.tests getDataFileName compiler optimization
                , PublicationTests.tests getDataFileName compiler optimization
                , SourceJudgmentTests.tests getDataFileName compiler optimization
                , OpaqueIdentityTests.tests compiler optimization
                ]
            | optimization <- [O0, O2]
            ]
