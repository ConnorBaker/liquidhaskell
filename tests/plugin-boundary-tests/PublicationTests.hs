module PublicationTests (tests) where

import CompilerFixture
import QueryAssertions (assertAuthoredFailure)
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase)

tests :: (FilePath -> IO FilePath) -> IO Compiler -> Optimization -> TestTree
tests fixture compiler optimization =
    testGroup
        "publication"
        [ scenario "raw verdict is independent of expected-failure presentation" $ \tool directory -> do
            raw <- producer tool directory "raw" "raw" (UnsafeAt [8]) Nothing []
            failed <- producer tool directory "fail" "fail" Safe (Just False) []
            client tool directory "fail" "Client" failed (UnsafeAt [8])
            mapM_ assertAuthoredFailure [raw, failed]
        , lawful "good"
        , lawful "private-good"
        , lawful "private-reflected"
        , rejected "private-bad" 4
        , -- A closed-False probe cannot discharge another binding's false post,
          -- regardless of source declaration order.
          rejected "closed-before" 8
        , rejected "closed-after" 4
        , trusted "compile-spec"
        , trusted "ignore"
        , scenario "incremental checks withhold publication until a full check" $ \tool directory -> do
            initial <- producer tool directory "diff" "good" Safe (Just True) ["--diff"]
            reused <- compile tool Strict optimization ObjectCode (compiledDirectory initial) "Producer" [] ["--diff"] Safe
            assertPublication tool reused False
            client tool directory "diff-reused" "ValidClient" reused (UnsafeAt [8])
            full <- compile tool Strict optimization ObjectCode (compiledDirectory initial) "Producer" [] ["--full"] Safe
            assertPublication tool full True
            client tool directory "diff-full" "ValidClient" full Safe
        ]
  where
    scenario label action = testCase label $ withSystemTempDirectory "lh-publication" $ \directory -> do
        tool <- compiler
        action tool directory
    lawful variant = scenario ("lawful " ++ variant ++ " publishes without proving a false client") $ \tool directory -> do
        compiled <- producer tool directory variant variant Safe (Just True) []
        client tool directory variant "Client" compiled (UnsafeAt [8])
        client tool directory variant "ValidClient" compiled Safe
    rejected variant owner = scenario (variant ++ " cannot hide an unrelated false claim") $ \tool directory -> do
        _ <- producer tool directory variant variant (UnsafeAt [owner]) Nothing []
        pure ()
    trusted variant = scenario (variant ++ " remains explicit trust") $ \tool directory -> do
        compiled <- producer tool directory variant variant Safe (Just True) []
        client tool directory variant "Client" compiled Safe
    producer tool directory label variant expected published options = do
        let target = directory </> label
        writeFixture (publication </> variant </> "Producer.hs") target "Producer" (producerSource variant)
        compiled <- compile tool Strict optimization ObjectCode target "Producer" [] options expected
        mapM_ (assertPublication tool compiled) published
        pure compiled
    client tool directory label name compiled expected = do
        let target = directory </> label </> name
        copyFixture fixture (publication </> name ++ ".hs") target name
        _ <- compile tool Strict optimization ObjectCode target name [compiledDirectory compiled </> "objects"] [] expected
        pure ()
    publication = "plugin-boundary-tests/fixtures/publication"

producerSource :: String -> String
producerSource variant = unlines $ case variant of
    "raw" -> reflected "1" ""
    "good" -> reflected "0" ""
    "fail" -> reflected "1" "{-@ fail f @-}"
    "ignore" -> reflected "1" "{-@ ignore f @-}"
    "compile-spec" -> reflected "1" "{-@ LIQUID \"--compile-spec\" @-}"
    "private-good" -> moduleLine : definition "0" ++ probe
    "private-bad" -> moduleLine : definition "1" ++ probe
    "closed-before" -> moduleLine : closed ++ definition "1"
    "closed-after" -> moduleLine : definition "1" ++ closed
    "private-reflected" -> reflected "0" "" ++ reflectedProbe
    _ -> error ("unknown publication fixture: " ++ variant)
  where
    moduleLine = "module Producer (f) where"
    definition result = ["{-@ f :: Integer -> {v:Integer | v == " ++ result ++ "} @-}", "f :: Integer -> Integer", "f _ = 0"]
    reflected result directive = ["{-@ LIQUID \"--reflection\" @-}", "{-@ LIQUID \"--ple\" @-}", moduleLine, directive, "{-@ reflect f @-}"] ++ definition result
    probe = ["{-@ fail _lhVacuityProbe @-}", "{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}", "_lhVacuityProbe :: Int -> Int", "_lhVacuityProbe x = x - 1"]
    closed = ["{-@ fail privateProbe @-}", "{-@ privateProbe :: {v:Integer | False} @-}", "privateProbe :: Integer", "privateProbe = 0"]
    reflectedProbe = ["", "{-@ fail _lhVacuityProbe @-}", "{-@ _lhVacuityProbe :: Int -> {v : Int | 0 < v} @-}", "_lhVacuityProbe :: Int -> Int", "_lhVacuityProbe probeArgument = probeArgument - 1"]
