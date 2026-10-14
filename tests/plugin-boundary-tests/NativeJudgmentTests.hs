module NativeJudgmentTests (tests) where

import CompilerFixture
import Control.Monad (void)
import qualified NativeRefinementFixtures as Fixtures
import System.IO.Temp (withSystemTempDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase)

tests :: IO Compiler -> Optimization -> TestTree
tests compiler optimization =
    testGroup
        "native method subtype judgments"
        [ sourceCase "NativeFalseDomain" Fixtures.falseDomain Safe
        , sourceCase "NativeTrueDomain" Fixtures.trueDomain (UnsafeAt [15])
        , sourceCase "NativeBadHelperBody" Fixtures.badHelperBody (UnsafeAt [8])
        , sourceCase "DistinctNativePredicates" Fixtures.distinctPredicates (UnsafeAt [9])
        , sourceCase "AlphaNativePredicates" Fixtures.alphaEquivalentPredicates Safe
        , sourceCase "NativeAggregatePrimitive" Fixtures.aggregatePrimitive Safe
        , sourceCase "NativeCallbackAlpha" Fixtures.alphaCallbackPredicate Safe
        , sourceCase "NativeCallbackDistinct" Fixtures.distinctCallbackPredicates (UnsafeAt [10])
        , sourceCase "NativeProjectedCallbackAlpha" Fixtures.alphaProjectedCallbackPredicate Safe
        , sourceCase "NativeProjectedCallbackDistinct" Fixtures.distinctProjectedCallbackPredicates (UnsafeAt [14])
        , sourceCase "NativeSameSpelledTermPredicate" Fixtures.sameSpelledTermPredicate Safe
        , sourceCase "NativeFalseMembership" Fixtures.falseMembershipGuard Safe
        , sourceCase "NativeInadmissibleMembership" Fixtures.inadmissibleMembershipGuard (UnsafeAt [5])
        , sourceCase "NativeClassFalseMembership" Fixtures.falseClassMembershipGuard Safe
        , sourceCase "NativeClassFormationOnly" Fixtures.inadmissibleClassMembershipGuard (UnsafeAt [5])
        , sourceCase "NativePrivateFalse" Fixtures.privateFalseDomain Safe
        , sourceCase "NativePrivateTrue" Fixtures.privateTrueDomain (UnsafeAt [12])
        , sourceCase "NativePrivateIdentity" Fixtures.privateIdentityDomain (UnsafeAt [12])
        , sourceCase "NativeTransitivePrivateFalse" Fixtures.transitivePrivateFalseDomain Safe
        , sourceCase "NativePendingDictionary" Fixtures.pendingDictionaryDomain (FormationRefusal 5 "Instance compatibility depends on unadmitted instance authority:")
        , sourceCase "NativeSharedMethods" Fixtures.consistentSharedMethods Safe
        , sourceCase "NativeSharedMethodsReversed" Fixtures.reversedConsistentSharedMethods Safe
        , sourceCase "NativeConflictingSharedMethods" Fixtures.conflictingSharedMethods (UnsafeAt [12])
        , sourceCase "NativeConflictingSharedMethodsReversed" Fixtures.reversedConflictingSharedMethods (UnsafeAt [15])
        ]
  where
    sourceCase name body expected =
        testCase name $ withSystemTempDirectory "lh-native-judgment" $ \directory -> do
            tool <- compiler
            writeFixture name directory name body
            void $ compile tool Strict optimization ObjectCode directory name [] [] expected
