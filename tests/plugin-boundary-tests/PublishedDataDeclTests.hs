module PublishedDataDeclTests (tests) where

import CompilerFixture
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase)

-- A module that reflects over another module's data type re-derives that type's
-- data declaration from GHC names. Their positions exist only for names GHC
-- created in the same session, so a dependent compiled with its dependency
-- loaded from an interface derives the declaration at "<no source information>".
-- The defining module publishes the declaration; if the dependent publishes it
-- too, a consumer of both generates the type's selectors twice at two positions
-- and rejects them as "Multiple measures". The re-export clients check that
-- the type's measures still reach a module that never imports the owner. The
-- Plain clients use a type from a module without a Liquid interface, reached
-- only through PlainDependent: PLE unfolding of its reflected function on a
-- constructed value, and a measure's fact on a constructed value without PLE.
-- The Refined clients rely on the owner's refined field.
tests :: (FilePath -> IO FilePath) -> IO Compiler -> Optimization -> TestTree
tests fixture compiler optimization =
    testGroup
        "published data declarations"
        [ scenario "consumer of the owner and a dependent compiled separately" $ \tool directory -> do
            owner <- module_ tool directory "owner" "Owner" [] Safe
            dependent <- module_ tool directory "dependent" "Dependent" [owner] Safe
            _ <- module_ tool directory "consumer" "Consumer" [owner, dependent] Safe
            pure ()
        , scenario "consumer of the owner and a dependent compiled with it" $ \tool directory -> do
            let session = directory </> "session"
            mapM_ (\name -> copy session name) ["Owner", "Dependent"]
            compileSession tool Strict optimization session ["Owner", "Dependent"]
            _ <- module_ tool directory "consumer" "Consumer" [session </> "objects"] Safe
            pure ()
        , scenario "clients reaching the type only through a re-export" $ \tool directory -> do
            owner <- module_ tool directory "owner" "Owner" [] Safe
            dependent <- module_ tool directory "dependent" "Dependent" [owner] Safe
            via <- module_ tool directory "via" "Via" [owner] Safe
            -- GHC reads Owner's interface to load Via's re-export, so it is on the
            -- search path; the clients import only Via and Dependent.
            _ <- module_ tool directory "good" "ViaClientGood" [via, dependent, owner] Safe
            _ <- module_ tool directory "false" "ViaClientFalse" [via, dependent, owner] (UnsafeAt [9])
            pure ()
        , scenario "a dependent republishes a type no dependency publishes" $ \tool directory -> do
            let plain = directory </> "plain"
            copy plain "Plain"
            _ <- compileHaskell tool optimization plain "Plain" []
            dependent <- module_ tool directory "dependent" "PlainDependent" [plain </> "objects"] Safe
            _ <- module_ tool directory "good" "PlainConsumerGood" [plain </> "objects", dependent] Safe
            _ <- module_ tool directory "false" "PlainConsumerFalse" [plain </> "objects", dependent] (UnsafeAt [9])
            mapM_
                (\(name, expected) -> module_ tool directory name name [plain </> "objects", dependent] expected)
                [("ConstructGood", Safe), ("ConstructFalse", UnsafeAt [9])]
        , scenario "a consumer relies on the owner's refined data definition" $ \tool directory -> do
            owner <- module_ tool directory "owner" "RefinedOwner" [] Safe
            dependent <- module_ tool directory "dependent" "RefinedDependent" [owner] Safe
            _ <- module_ tool directory "good" "RefinedConsumerGood" [owner, dependent] Safe
            _ <- module_ tool directory "false" "RefinedConsumerFalse" [owner, dependent] (UnsafeAt [9])
            pure ()
        ]
  where
    scenario label action = testCase label $ withSystemTempDirectory "lh-published-datadecls" $ \directory -> do
        tool <- compiler
        action tool directory
    copy target name = copyFixture fixture ("plugin-boundary-tests/fixtures/published-datadecls" </> name ++ ".hs") target name
    -- Compile one module in its own directory; return the directory of its
    -- interface for the modules that import it.
    module_ tool directory subdirectory name imports expected = do
        let target = directory </> subdirectory
        copy target name
        _ <- compile tool Strict optimization ObjectCode target name imports [] expected
        pure (target </> "objects")
