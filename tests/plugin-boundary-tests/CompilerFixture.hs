module CompilerFixture (
    Compiler,
    Optimization (..),
    CheckingMode (..),
    Backend (..),
    Expectation (..),
    Compiled (..),
    configuredCompiler,
    withPackageDatabase,
    copyFixture,
    writeFixture,
    compile,
    compileHaskell,
    assertMissingTotalityPolicy,
    assertPublication,
    assertSourceNameAbsent,
    assertSourceNamePresent,
) where

import Data.Char (isDigit, toLower)
import Data.List (isInfixOf, isPrefixOf, nub, sort, tails)
import System.Directory (createDirectoryIfMissing, doesFileExist)
import System.Environment (getEnvironment, lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath (isAbsolute, takeDirectory, takeFileName, (</>))
import System.Process (CreateProcess (..), proc, readCreateProcessWithExitCode)
import System.Timeout (timeout)
import Test.Tasty.HUnit (assertBool, assertFailure, (@?=))
import Text.Read (readMaybe)

data Compiler = Compiler FilePath String [(String, String)] [String]

data Optimization = O0 | O2 deriving (Show)

data CheckingMode = Strict | WithoutRefinementChecking | WithoutDerivedChecking

data Backend = ObjectCode | InterfaceOnly deriving (Show)

data Expectation
    = Safe
    | UnsafeAt [Int]
    | TerminationAt [Int]
    | TerminationCheckAt [Int]
    | FailureAt [Int]
    | FormationRefusal Int String
    | DependencyAmbiguity String [String]

data Compiled = Compiled
    { compiledDirectory :: FilePath
    , compiledModule :: String
    }

-- The command owns the matched compiler/plugin tuple. No fallback to another
-- compiler, expected-error status, or loader tracing establishes that ownership.
configuredCompiler :: IO Compiler
configuredCompiler = do
    supplied <- lookupEnv "LIQUID_TEST_GHC"
    ghc <- case supplied of
        Just path | isAbsolute path -> pure path
        _ -> assertFailure "set LIQUID_TEST_GHC to the matching installed GHC executable" >> fail "missing compiler"
    exists <- doesFileExist ghc
    assertBool ("missing compiler: " ++ ghc) exists
    environment <- getEnvironment
    let clean = ("GHC_ENVIRONMENT", "-") : filter ((`notElem` ["GHC_ENVIRONMENT", "LIQUIDHASKELL_OPTS"]) . fst) environment
        packageTool = takeDirectory ghc </> "ghc-pkg"
    (status, output) <- command clean Nothing packageTool ["--global", "field", "liquidhaskell", "id", "--simple-output"]
    status @?= ExitSuccess
    unit <- case words output of
        [one] -> pure one
        _ -> assertFailure ("expected exactly one installed liquidhaskell unit: " ++ output) >> fail "ambiguous plugin unit"
    pure (Compiler ghc unit clean [])

-- Keep the selected compiler and plugin unit; only extend its package search
-- environment for the lifetime of the caller's temporary fixture bracket.
withPackageDatabase :: Compiler -> FilePath -> [FilePath] -> IO Compiler
withPackageDatabase (Compiler ghc unit environment arguments) database configurations = do
    let tool = takeDirectory ghc </> "ghc-pkg"
        run arguments = do
            (status, output) <- command environment Nothing tool arguments
            assertBool output (status == ExitSuccess)
    run ["init", database]
    mapM_ (\configuration -> run ["--package-db", database, "register", configuration]) configurations
    pure $ Compiler ghc unit environment $ arguments ++ ["-package-db", database, "-hide-all-plugin-packages"]

copyFixture :: (FilePath -> IO FilePath) -> FilePath -> FilePath -> String -> IO ()
copyFixture fixture relative directory name = do
    source <- fixture relative
    text <- readFile source
    writeFixture relative directory name text

writeFixture :: String -> FilePath -> String -> String -> IO ()
writeFixture relative directory name text = do
    assertBool
        ("optimization must be a runner parameter: " ++ relative)
        (not ("OPTIONS_GHC" `isInfixOf` text))
    createDirectoryIfMissing True directory
    writeFile (directory </> name ++ ".hs") text

compile :: Compiler -> CheckingMode -> Optimization -> Backend -> FilePath -> String -> [FilePath] -> [String] -> Expectation -> IO Compiled
compile (Compiler ghc unit environment packageArguments) checking optimization backend directory name imports options expected = do
    let objects = directory </> "objects"
        arguments =
            packageArguments
                ++ [ "-c"
                   , "-" ++ show optimization
                   , "-fforce-recomp"
                   , "-XGHC2024"
                   , "-no-user-package-db"
                   , "-hide-package"
                   , "liquidhaskell"
                   , "-plugin-package-id"
                   , unit
                   , "-fplugin=LiquidHaskell"
                   , "-fdiagnostics-color=never"
                   , -- Keep compiler scratch files under the fixture's cleanup bracket.
                     "-tmpdir"
                   , objects
                   , "-i"
                   , "-i."
                   ]
                ++ case backend of
                    ObjectCode -> []
                    InterfaceOnly -> ["-fno-code", "-fwrite-interface"]
                ++ map ("-i" ++) imports
                ++ map ("-fplugin-opt=LiquidHaskell:" ++) (checkingOptions checking ++ options)
                ++ ( case backend of
                        ObjectCode -> ["-o", objects </> name ++ ".o"]
                        InterfaceOnly -> []
                   )
                ++ ["-ohi", objects </> name ++ ".hi", name ++ ".hs"]
    createDirectoryIfMissing True objects
    (status, output) <- command environment (Just directory) ghc arguments
    let context = takeFileName directory ++ " / " ++ name ++ " / " ++ show optimization ++ " / " ++ show backend ++ "\n" ++ output
        results = [words rest | line <- lines output, Just rest <- [after "LIQUID: " line]]
        diagnostics = [line | line <- lines output, ": error:" `isInfixOf` line]
        ownerLines = sort . nub $ [n | line <- diagnostics, Just location <- [after (name ++ ".hs:") line], Just n <- [readMaybe (takeWhile isDigit location)]]
        unsafeResult owners category = do
            assertBool context (status == ExitFailure 1)
            assertBool context (verdict "UNSAFE" results)
            assertBool context (not (null diagnostics) && all (isPrefixOf (name ++ ".hs:")) diagnostics)
            assertBool context (ownerLines == sort (nub owners))
            assertBool context (category `isInfixOf` output)
            assertBool context (not ("panic" `isInfixOf` map toLower output))
            emitted <- doesFileExist (objects </> name ++ ".hi")
            assertBool (context ++ "\nfailed source emitted an interface") (not emitted)
    assertBool context $
        not $
            any
                (`isInfixOf` map toLower output)
                ( ["<<timeout>>", "internal error", "segmentation fault", "stack overflow", "heap exhausted", "<command line>"]
                    ++ case expected of
                        DependencyAmbiguity _ _ -> []
                        _ -> ["<no location info>"]
                )
    case expected of
        Safe -> do
            safeResult context status results diagnostics
            case backend of
                ObjectCode -> pure ()
                InterfaceOnly -> do
                    emitted <- doesFileExist (objects </> name ++ ".o")
                    assertBool (context ++ "\ninterface-only compilation emitted object code") (not emitted)
        UnsafeAt owners -> unsafeResult owners "Liquid Type Mismatch"
        TerminationAt owners -> unsafeResult owners "Termination Error"
        TerminationCheckAt owners -> unsafeResult owners "Termination Check"
        FailureAt owners -> unsafeResult owners "Failure Error"
        FormationRefusal owner message -> do
            assertBool context (status == ExitFailure 1)
            assertBool context (message `isInfixOf` output)
            assertBool context (not (null diagnostics) && all (isInfixOf (name ++ ".hs:")) diagnostics)
            assertBool context (ownerLines == [owner])
            assertBool context (not (any (\entry -> take 1 entry `elem` [["SAFE"], ["UNSAFE"]]) results))
            emitted <- doesFileExist (objects </> name ++ ".hi")
            assertBool (context ++ "\nmalformed source emitted an interface") (not emitted)
        DependencyAmbiguity moduleName providers -> do
            let ambiguities =
                    [ unlines (takeWhile (not . null) block)
                    | block@(line : _) <- tails (lines output)
                    , "ambiguous module name" `isInfixOf` map toLower line
                    , moduleName `isInfixOf` line
                    ]
            assertBool context (status == ExitFailure 1)
            assertBool context (not ("panic" `isInfixOf` map toLower output))
            assertBool context (any (\block -> all (`isInfixOf` block) providers) ambiguities)
            assertBool context (null results)
            emitted <- doesFileExist (objects </> name ++ ".hi")
            assertBool (context ++ "\nambiguous dependency emitted an interface") (not emitted)
    pure (Compiled directory name)
  where
    verdict wanted [actual : count : "constraints" : "checked)" : decoration] =
        actual == wanted
            && all (all (== '*')) decoration
            && maybe False (>= (0 :: Int)) (readMaybe (dropWhile (== '(') count))
    verdict _ _ = False
    safeResult context status results diagnostics = do
        assertBool context (status == ExitSuccess)
        assertBool context (null diagnostics)
        -- The banner counts candidate/target validity checks, not source obligations.
        -- Publication and the independent clients below test admission.
        assertBool context (verdict "SAFE" results)
        assertBool context (not ("panic" `isInfixOf` map toLower context))

strictOptions :: [String]
strictOptions = checkingOptions Strict

checkingOptions :: CheckingMode -> [String]
checkingOptions checking =
    ["--total-Haskell"]
        ++ ( case checking of
                Strict -> ["--check-derived", "--check-refinements"]
                WithoutRefinementChecking -> ["--check-derived"]
                WithoutDerivedChecking -> ["--check-refinements"]
           )
        ++ ["--no-annotations", "--save-query"]

-- The boot plugin can load without the assumptions package, but strict checking
-- must refuse that configuration before checking or publishing the source.
assertMissingTotalityPolicy :: Compiler -> Optimization -> FilePath -> String -> IO ()
assertMissingTotalityPolicy (Compiler ghc _ environment packageArguments) optimization directory name = do
    (packageStatus, packageOutput) <- command environment Nothing (takeDirectory ghc </> "ghc-pkg") ["--global", "field", "liquidhaskell-boot", "id", "--simple-output"]
    packageStatus @?= ExitSuccess
    boot <- case words packageOutput of
        [one] -> pure one
        _ -> assertFailure ("expected exactly one installed liquidhaskell-boot unit: " ++ packageOutput) >> fail "ambiguous boot unit"
    let objects = directory </> "objects"
        arguments =
            [ "-c"
            , "-" ++ show optimization
            , "-fforce-recomp"
            , "-XGHC2024"
            , "-no-user-package-db"
            , "-hide-all-packages"
            , "-hide-all-plugin-packages"
            , "-package"
            , "base"
            , "-package"
            , "ghc-internal"
            , "-package"
            , "ghc-prim"
            , "-plugin-package-id"
            , boot
            , "-fplugin=LiquidHaskellBoot"
            , "-fdiagnostics-color=never"
            , "-tmpdir"
            , objects
            , "-i"
            , "-i."
            ]
                ++ map ("-fplugin-opt=LiquidHaskellBoot:" ++) (strictOptions ++ ["--higherorder"])
                ++ ["-o", objects </> name ++ ".o", "-ohi", objects </> name ++ ".hi", name ++ ".hs"]
    createDirectoryIfMissing True objects
    (status, output) <- command environment (Just directory) ghc (packageArguments ++ arguments)
    let context = name ++ " / " ++ show optimization ++ "\n" ++ output
        diagnostic = "LiquidHaskell totality policy is unavailable; expose the liquidhaskell package with its compiled LH assumptions."
    assertBool context (status == ExitFailure 1)
    assertBool context (diagnostic `isInfixOf` unwords (words output))
    assertBool context $
        not $
            any
                (`isInfixOf` map toLower output)
                ["liquid: safe", "liquid: unsafe", "panic", "<<timeout>>", "internal error", "segmentation fault", "stack overflow", "heap exhausted"]
    emitted <- doesFileExist (objects </> name ++ ".hi")
    assertBool (context ++ "\nmissing totality policy emitted an interface") (not emitted)

-- External dependencies need not carry a Liquid interface. Keep this boundary
-- distinct from the verifier's SAFE judgment and explicitly check its absence.
compileHaskell :: Compiler -> Optimization -> FilePath -> String -> [String] -> IO Compiled
compileHaskell tool@(Compiler ghc _ environment packageArguments) optimization directory name options = do
    let objects = directory </> "objects"
    createDirectoryIfMissing True objects
    (status, output) <-
        command
            environment
            (Just directory)
            ghc
            ( [ "-c"
              , "-" ++ show optimization
              , "-fforce-recomp"
              , "-XGHC2024"
              , "-no-user-package-db"
              , "-tmpdir"
              , objects
              , "-i"
              , "-i."
              , "-o"
              , objects </> name ++ ".o"
              , "-ohi"
              , objects </> name ++ ".hi"
              , name ++ ".hs"
              ]
                ++ options
                ++ packageArguments
            )
    assertBool output (status == ExitSuccess)
    let compiled = Compiled directory name
    assertPublication tool compiled False
    pure compiled

assertPublication :: Compiler -> Compiled -> Bool -> IO ()
assertPublication (Compiler ghc _ environment packageArguments) compiled expected = do
    let name = compiledModule compiled
        interface = compiledDirectory compiled </> "objects" </> name ++ ".hi"
    (status, output) <- command environment Nothing ghc (packageArguments ++ ["--show-iface", interface])
    status @?= ExitSuccess
    let annotations = [line | line <- lines output, ("Module target " ++ name ++ " annotated by ") `isPrefixOf` line, "of type PayloadMarker" `isInfixOf` line]
    length annotations @?= if expected then 1 else 0

assertSourceNameAbsent :: Compiler -> Compiled -> String -> IO ()
assertSourceNameAbsent (Compiler ghc _ environment packageArguments) compiled name = do
    let interface = compiledDirectory compiled </> "objects" </> compiledModule compiled ++ ".hi"
    (status, output) <- command environment Nothing ghc (packageArguments ++ ["--show-iface", interface])
    status @?= ExitSuccess
    assertBool ("logical-only private name survived in GHC interface: " ++ name ++ "\n" ++ output) (not $ name `isInfixOf` output)

assertSourceNamePresent :: Compiler -> Compiled -> String -> IO ()
assertSourceNamePresent (Compiler ghc _ environment packageArguments) compiled name = do
    let interface = compiledDirectory compiled </> "objects" </> compiledModule compiled ++ ".hi"
    (status, output) <- command environment Nothing ghc (packageArguments ++ ["--show-iface", interface])
    status @?= ExitSuccess
    assertBool ("runtime-referenced private name absent from GHC interface: " ++ name ++ "\n" ++ output) (name `isInfixOf` output)

command :: [(String, String)] -> Maybe FilePath -> FilePath -> [String] -> IO (ExitCode, String)
command environment directory executable arguments = do
    result <-
        timeout (90 * 1000000) $
            readCreateProcessWithExitCode (proc executable arguments){cwd = directory, env = Just environment} ""
    case result of
        Nothing -> assertFailure ("compiler command timed out: " ++ unwords (executable : arguments)) >> fail "timeout is not a rejection"
        Just (status, output, errors) -> pure (status, stripAnsi (output ++ errors))

-- GHC's diagnostic-color flag does not govern the plugin's status banner.
stripAnsi :: String -> String
stripAnsi ('\ESC' : '[' : rest) = stripAnsi (drop 1 (dropWhile (\c -> c < '@' || c > '~') rest))
stripAnsi (first : rest) = first : stripAnsi rest
stripAnsi [] = []

after :: String -> String -> Maybe String
after needle text = case filter (isPrefixOf needle) (tails text) of
    first : _ -> Just (drop (length needle) first)
    [] -> Nothing
