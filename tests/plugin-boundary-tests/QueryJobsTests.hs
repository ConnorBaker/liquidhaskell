module QueryJobsTests (tests) where

import CompilerFixture
import Control.Monad (forM)
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as B8
import Data.List (isInfixOf, isPrefixOf, sort)
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))

-- Checking a module's independent proof groups at once must not change
-- anything the sequential fold reports or asks: the same exit status and
-- transcript, and the same saved fixpoint queries, byte for byte. The one
-- exception is the solver's own "Saving ..." notices for --save-query, printed
-- as each query is solved: the same notices, in completion order. The fixtures
-- cover callables inferred by one group and consumed by later ones, several
-- failing groups (some of them false values other groups must not assume),
-- rewrite rules, expected failures, instance method contracts and interface
-- rows, and solved types carried across queries.
tests :: (FilePath -> IO FilePath) -> IO Compiler -> Optimization -> TestTree
tests fixture compiler optimization =
    testGroup
        "query jobs"
        [ testCase (directory </> name) $ do
            tool <- compiler
            (status, output, queries) <- run tool directory name options "1" []
            (status', output', queries') <- run tool directory name options "4" ["+RTS", "-N4", "-RTS"]
            let context = name ++ " / " ++ show optimization ++ "\n--- one job\n" ++ output ++ "\n--- four jobs\n" ++ output'
            assertBool (context ++ "\nno query was saved") (not (null queries))
            assertBool context (not ("panic" `isInfixOf` output))
            status' @?= status
            assertBool context (reported output' == reported output)
            sort (notices output') @?= sort (notices output)
            map fst queries' @?= map fst queries
            mapM_ (\((file, text), (_, text')) -> assertBool ("saved query differs: " ++ file) (text' == text)) (zip queries queries')
        | (directory, name, options) <- fixtures
        ]
  where
    run tool directory name options jobs extra = withSystemTempDirectory "lh-query-jobs" $ \scratch -> do
        let target = scratch </> "fixture"
            saved = target </> ".liquid"
        copyFixture fixture ("plugin-boundary-tests/fixtures" </> directory </> name ++ ".hs") target name
        (status, output) <- transcript tool Strict optimization target name (options ++ ["--query-jobs=" ++ jobs]) extra
        exists <- doesDirectoryExist saved
        files <- if exists then sort <$> listDirectory saved else pure []
        queries <- forM files $ \file -> do
            bytes <- B.readFile (saved </> file)
            pure (file, replaceBytes (B8.pack scratch) (B8.pack "<scratch>") bytes)
        length output `seq` pure (status, replace scratch "<scratch>" output, queries)
    reported = filter (not . notice) . lines
    notices = filter notice . lines
    notice line = "Saving " `isPrefixOf` dropWhile (== ' ') line
    replace needle substitute = go
      where
        go [] = []
        go text@(c : rest)
            | needle `isPrefixOf` text = substitute ++ go (drop (length needle) text)
            | otherwise = c : go rest
    replaceBytes needle substitute = B.concat . go
      where
        go bytes = case B.breakSubstring needle bytes of
            (before, rest)
                | B.null rest -> [before]
                | otherwise -> before : substitute : go (B.drop (B.length needle) rest)
    rewrites = ["--reflection", "--ple"]
    fixtures =
        [ ("inferred-interface", "InferredFunctionGood", [])
        , ("inferred-interface", "InferredFunctionFalse", [])
        , ("inferred-interface", "InferredHoleGood", [])
        , ("group-failures", "GroupFailuresIndependent", [])
        , ("group-failures", "GroupFailuresExpectedSafe", [])
        , ("group-failures", "GroupFailuresAuthoredBody", [])
        , ("group-failures", "GroupFailuresFalseValueFirst", [])
        , ("group-failures", "GroupFailuresFalseValueLast", [])
        , ("rewrite-dependencies", "ExplicitRewriteCycleFalse", rewrites)
        , ("rewrite-dependencies", "MediatedRewriteCycleFalse", rewrites)
        , ("rewrite-dependencies", "RewriteUserFirstGood", rewrites)
        , ("expected-claims", "ExpectedMeasureAfter", [])
        , ("expected-claims", "StagedMeasureCycleGood", [])
        , ("dictionary-methods", "PickContractGood", [])
        , ("dictionary-methods", "SuperclassContractGood", [])
        , ("dictionary-methods", "SuperclassFabFalse", [])
        , ("noncut-export", "NoncutExportShow", ["--environment-reduction"])
        , ("noncut-export", "NoncutExportNoShowBad", ["--environment-reduction"])
        ]
