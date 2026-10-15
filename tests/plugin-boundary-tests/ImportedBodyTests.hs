module ImportedBodyTests (tests) where

import CompilerFixture
import SourceVariantFixtures (copySourceFixture)
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase)

-- A raw GHC interface supplies executable source, not a Liquid theorem.
-- The same executor checks its selected original owner and independent clients.
tests :: (FilePath -> IO FilePath) -> IO Compiler -> Optimization -> TestTree
tests fixture compiler optimization =
    testGroup
        "owned imported bodies"
        [ scenario "original body admission, authored diagnostics, and fresh publication" $ \tool directory -> do
            provider <- raw tool directory "OwnedIdentityProvider"
            good <- checked tool directory "OwnedIdentityGood" [provider] Safe
            assertPublication tool good True
            assertSourceNamePresent tool good "OwnedIdentityProvider.ownedIdentity"
            _ <- checked tool directory "OwnedIdentityBad" [provider] (UnsafeAt [5])
            _ <- checked tool directory "OwnedFreshGood" [provider, good] Safe
            _ <- checked tool directory "OwnedFreshWrong" [provider, good] (UnsafeAt [7])
            _ <- checked tool directory "OwnedFreshNoProof" [provider] (UnsafeAt [7])
            pure ()
        , scenario "qualification and local dotted operators preserve original ownership" $ \tool directory -> do
            identity <- raw tool directory "OwnedIdentityProvider"
            alternative <- raw tool directory "OwnedAlternativeProvider"
            operator <- raw tool directory "DotColonProvider"
            _ <- checked tool directory "OwnedQualified" [identity] Safe
            _ <- checked tool directory "OwnedOperatorGood" [operator] Safe
            _ <- checked tool directory "OwnedOperatorBad" [operator] (UnsafeAt [5])
            _ <- checked tool directory "LocalOnly" [] Safe
            _ <- checked tool directory "LocalDot" [] Safe
            _ <- checked tool directory "LocalColonGood" [operator] Safe
            -- A real local body position must win over its authored claim.
            _ <- checked tool directory "LocalColonBad" [operator] (UnsafeAt [11])
            _ <- checked tool directory "OwnedAmbiguous" [identity, alternative] (FormationRefusal 6 "Ambiguous imported body owner")
            pure ()
        , scenario "reachable helpers and strict refinement domains cannot self-authorize" $ \tool directory -> do
            identity <- raw tool directory "OwnedIdentityProvider"
            helper <- raw tool directory "OwnedHelperProvider"
            -- The guard exercises a genuine retained dependency, not a helper
            -- optimized away from the selected owner's source unfolding.
            assertSourceNamePresent tool helper "Unfolding: Core: StableUser <1,FalseTrue> hydratedHelper"
            assertSourceNamePresent tool helper "Unfolding: Core: <vanilla>"
            helperGood <- checked tool directory "OwnedHelperGood" [helper] Safe
            assertPublication tool helperGood True
            assertSourceNamePresent tool helperGood "OwnedHelperProvider.ownedNested"
            _ <- checked tool directory "OwnedHelperBad" [helper] (UnsafeAt [5])
            _ <- checked tool directory "OwnedHelperAssumed" [helper] (FormationRefusal 5 "hydratedHelper also has an authored assumption")
            _ <- checked tool directory "OwnedIgnored" [identity] (FormationRefusal 5 "is authored ignored")
            _ <- checked tool directory "OwnedLazy" [identity] (FormationRefusal 5 "has an authored termination waiver")
            _ <- checked tool directory "OwnedFail" [identity] (FormationRefusal 5 "has an authored expected-failure annotation")
            _ <- checked tool directory "OwnedRefinementDomain" [identity] (UnsafeAt [5])
            let target = directory </> "without-refinement-checking"
            copy target "OwnedRefinementDomain"
            _ <- compile tool WithoutRefinementChecking optimization InterfaceOnly target "OwnedRefinementDomain" [compiledDirectory identity </> "objects"] [] (FormationRefusal 5 "requires complete strict source checking")
            _ <- checked tool directory "OwnedWithText" [] (FormationRefusal 7 "unpackAppendCString# has neither an actual unfolding nor a retained dependency contract")
            pure ()
        , scenario "imported generated binders are checked with or without derived checking" $ \tool directory -> do
            complete <- raw tool directory "GeneratedHelperProvider"
            partial <- raw tool directory "GeneratedHelperPartialProvider"
            -- The selected owner reaches a generated instance-method binder.
            assertSourceNamePresent tool complete "StableUser <2,FalseTrue> $fPickBool_$cpick"
            assertSourceNamePresent tool partial "StableUser <2,FalseTrue> $fPickBool_$cpick"
            _ <- checked tool directory "GeneratedHelperGood" [complete] Safe
            _ <- checked tool directory "GeneratedHelperBad" [partial] (UnsafeAt [5])
            -- --check-derived governs only this module's generated binders.
            -- An imported body is source to check, never derived trust.
            _ <- withoutDerived tool directory "GeneratedHelperGood" [complete] Safe
            _ <- withoutDerived tool directory "GeneratedHelperBad" [partial] (UnsafeAt [5])
            pure ()
        ]
  where
    scenario label action = testCase label $ withSystemTempDirectory "lh-imported-owned" $ \directory -> compiler >>= \tool -> action tool directory
    copy directory name = copySourceFixture fixture ("plugin-boundary-tests/fixtures/imported-owned" </> name ++ ".hs") directory name
    raw tool directory name = do
        let target = directory </> name
        copy target name
        compileHaskell tool optimization target name ["-fno-omit-interface-pragmas", "-fexpose-all-unfoldings"]
    withoutDerived tool directory name providers expected = do
        let target = directory </> "without-derived-checking" </> name
        copy target name
        compile tool WithoutDerivedChecking optimization InterfaceOnly target name [compiledDirectory provider </> "objects" | provider <- providers] [] expected
    checked tool directory name providers expected = do
        let target = directory </> name
        copy target name
        compile tool Strict optimization InterfaceOnly target name [compiledDirectory provider </> "objects" | provider <- providers] [] expected
