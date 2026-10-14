module QueryAssertions (assertAuthoredFailure, assertDefaultInterfaces, assertExternalFormationTag, assertSingleSourceCheck, assertJointInferenceCheck, compatibilityObligations) where

import CompilerFixture (Compiled (..))
import qualified Data.ByteString as ByteString
import Data.Foldable (toList)
import Data.List (isPrefixOf, isSuffixOf)
import qualified Data.Store as Store
import qualified Language.Fixpoint.Solver as Solver
import qualified Language.Fixpoint.Types as F
import qualified Language.Fixpoint.Types.Config as C
import System.Directory (doesFileExist, listDirectory)
import System.FilePath ((</>))
import System.Timeout (timeout)
import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, (@?=))

-- IgnoredNestedGood's ordinary binding has a complete result=0 interface.
-- Its body and formation must be checked, without first inferring another
-- result that the authored query will not use. Other generated Core groups
-- may still need inference; identify this actual goal rather than count files.
assertSingleSourceCheck :: Compiled -> Assertion
assertSingleSourceCheck = assertOneAuthoredQuery (resultGoal 0)

-- The unsigned/holey helper and its signed consumer share inference variables,
-- not a circular proof. Check the consumer's actual increment goal once; an
-- earlier independent solve of that same group is redundant.
assertJointInferenceCheck :: Compiled -> Assertion
assertJointInferenceCheck = assertOneAuthoredQuery incrementGoal
  where
    incrementGoal constraint = case F.srhs constraint of
        F.RR sort (F.Reft (value, predicate)) ->
            sort == F.intSort && any (increment value) (F.conjuncts predicate)
    increment value (F.PAtom F.Eq (F.EVar result) (F.EBin F.Plus (F.EVar _) (F.ECon (F.I 1)))) = result == value
    increment _ _ = False

-- Shared dictionaries have fixed default interfaces. Both consumers need
-- one authored check, whether those checks are solved separately or as an
-- ordered conjunction. Query-file separation is not an interface property.
assertDefaultInterfaces :: Compiled -> Assertion
assertDefaultInterfaces compiled =
    mapM_
        (\(lower, upper) -> assertOneAuthoredQuery (rangeGoal lower upper) compiled)
        [(0, 1), (2, 3)]
  where
    -- Source && retains conditional demand in the lowered predicate.
    rangeGoal lower upper constraint = case F.srhs constraint of
        F.RR sort (F.Reft (value, predicate)) ->
            sort == F.intSort
                && F.EIte
                    (F.PAtom F.Le (F.ECon (F.I lower)) (F.EVar value))
                    (F.EIte (F.PAtom F.Le (F.EVar value) (F.ECon (F.I upper))) F.PTrue F.PFalse)
                    F.PFalse
                    `elem` F.conjuncts predicate

assertOneAuthoredQuery :: (F.SubC () -> Bool) -> Compiled -> Assertion
assertOneAuthoredQuery goal compiled = do
    let directory = compiledDirectory compiled </> ".liquid"
        modulePrefix = compiledModule compiled ++ ".hs."
        checkingPrefix = modulePrefix ++ "checking."
    queries <- checkingQueries compiled
    let matches = [file | (file, query) <- queries, any goal (F.cm query)]
    case matches of
        [file] -> do
            admitted <- doesFileExist (directory </> modulePrefix ++ "admission." ++ drop (length checkingPrefix) file)
            assertBool "acyclic source judgment was independently inferred before checking" (not admitted)
        other -> assertFailure ("expected exactly one authored query for the goal, got " ++ show other)

resultGoal :: Integer -> F.SubC () -> Bool
resultGoal expected constraint =
    case F.srhs constraint of
        F.RR sort (F.Reft (value, predicate)) ->
            sort == F.intSort
                && F.conjuncts predicate == [F.PAtom F.Eq (F.EVar value) (F.ECon (F.I expected))]

-- The imported `ord` declaration has no local call-graph tag. Its predicate's
-- positive-argument obligation must not inherit the last local function's tag.
-- A declaration without a local body is checked in the `.declarations` stage.
assertExternalFormationTag :: Compiled -> Assertion
assertExternalFormationTag compiled = do
    let path = compiledDirectory compiled </> ".liquid" </> compiledModule compiled ++ ".hs.declarations.bfq"
    query <- readQuery path
    let tags =
            [ F.stag constraint
            | constraint <- toList (F.cm query)
            , F.RR sort (F.Reft (value, predicate)) <- [F.srhs constraint]
            , sort == F.intSort
            , F.PAtom F.Lt (F.ECon (F.I 0)) (F.EVar value) `elem` F.conjuncts predicate
            ]
    assertBool "missing external assumption's positive-argument obligation" (not (null tags))
    mapM_ (@?= [0]) tags

-- This fixture has exactly one authored failing postcondition: its own result
-- equals 1. Generated names and unrelated premises are not part of that goal.
-- Parse the complete saved query, then require its actual raw solver failure;
-- the compiler test separately checks the source owner and presented verdict.
assertAuthoredFailure :: Compiled -> Assertion
assertAuthoredFailure compiled = do
    let directory = compiledDirectory compiled
    queries <- map snd <$> checkingQueries compiled
    let goals =
            [ (query, F.subcId constraint)
            | query <- queries
            , constraint <- toList (F.cm query)
            , resultGoal 1 constraint
            ]
        config =
            C.defConfig
                { C.srcFile = directory </> "replayed-goal.fq"
                , C.cores = Just 1
                , C.noStringTheory = True
                , C.noEnvReduction = True
                }
    case goals of
        [(query, identifier)] -> do
            result <- timeout (90 * 1000000) (Solver.solve config query)
            case F.resStatus <$> result of
                Just (F.Unsafe _ failures) -> map fst failures @?= [identifier]
                other -> assertFailure ("expected the authored saved-query failure, got " ++ show other)
        other -> assertFailure ("expected exactly one authored result=1 goal, got " ++ show (map snd other))

-- The constraints of a module's instance-against-class compatibility query.
-- Only a module's own instance declarations are its obligations there.
compatibilityObligations :: Compiled -> IO Int
compatibilityObligations compiled =
    length . F.cm <$> readQuery (compiledDirectory compiled </> ".liquid" </> compiledModule compiled ++ ".hs.compatibility.bfq")

checkingQueries :: Compiled -> IO [(FilePath, F.FInfo ())]
checkingQueries compiled = do
    let directory = compiledDirectory compiled </> ".liquid"
        prefix = compiledModule compiled ++ ".hs.checking."
    files <- listDirectory directory
    mapM
        (\file -> (,) file <$> readQuery (directory </> file))
        [file | file <- files, prefix `isPrefixOf` file, ".bfq" `isSuffixOf` file]

-- Use the saved AST, not its presentation syntax: generated qualifiers may
-- contain existentials, which the default text-query reader does not accept.
readQuery :: FilePath -> IO (F.FInfo ())
readQuery path = do
    bytes <- ByteString.readFile path
    case Store.decode bytes of
        Right query -> pure query
        Left err -> assertFailure (path ++ ": " ++ show err) >> fail "invalid saved query"
