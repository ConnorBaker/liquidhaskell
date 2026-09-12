module AnnotationIdentityTests (tests, crossUnitTests) where

import Data.Proxy (Proxy (..))
import Data.Typeable (TypeRep, tyConModule, tyConName, tyConPackage, typeRep, typeRepTyCon)
import Data.Word (Word8)
import GHC.Serialized (Serialized (..), toSerialized)
import Language.Haskell.Liquid.GHC.Plugin.AnnotationIdentity
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))

newtype Payload = Payload [Word8]

tests :: TestTree
tests =
    testGroup
        "annotation identity"
        [ testCase "no annotation is missing" $ select [] @?= Right Nothing
        , testCase "unrelated annotation is ignored" $ select [unrelated] @?= Right Nothing
        , testCase "exact current nominal type is selected" $ select [current] @?= Right (Just [1, 2, 3])
        , testCase "unrelated before current is ignored" $ select [unrelated, current] @?= Right (Just [1, 2, 3])
        , testCase "unrelated after current is ignored" $ select [current, unrelated] @?= Right (Just [1, 2, 3])
        , testCase "duplicate current annotations fail closed" $ select [current, unrelated, current] @?= Left DuplicateAnnotations
        , testCase "recognized corrupt bytes are not missing" $ select [Serialized expected []] @?= Right (Just [])
        , testCase "unrelated payload is not inspected" $ select [Serialized (typeRep (Proxy :: Proxy Int)) (error "unrelated payload forced"), current] @?= Right (Just [1, 2, 3])
        ]
  where
    expected = typeRep (Proxy :: Proxy Payload)
    select = selectAnnotationPayload expected
    current = toSerialized (\(Payload bytes) -> bytes) (Payload [1, 2, 3])
    unrelated = toSerialized (const [9]) (42 :: Int)

-- The registered test entrypoint supplies real TypeReps from two private Cabal
-- libraries compiling the same declaration under distinct unit IDs. No synthetic
-- TyCon or TypeRep is manufactured to exercise the cross-unit boundary.
crossUnitTests :: TypeRep -> TypeRep -> TestTree
crossUnitTests old current =
    testGroup
        "real cross-unit annotation identity"
        [ testCase "same declaration has distinct unit-dependent TypeReps" $ do
            tyConModule (typeRepTyCon old) @?= tyConModule (typeRepTyCon current)
            tyConName (typeRepTyCon old) @?= tyConName (typeRepTyCon current)
            assertBool "unit IDs must differ" (tyConPackage (typeRepTyCon old) /= tyConPackage (typeRepTyCon current))
            assertBool "nominal TypeReps must differ" (old /= current)
        , testCase "old unit is rejected without decoding bytes" $
            selectAnnotationPayload current [Serialized old (error "stale payload forced")] @?= Left stale
        , testCase "current before old still rejects stale" $
            selectAnnotationPayload current [Serialized current [1], Serialized old [2]] @?= Left stale
        , testCase "old before current still rejects stale" $
            selectAnnotationPayload current [Serialized old [2], Serialized current [1]] @?= Left stale
        , testCase "same-name current unit accepted exactly" $
            selectAnnotationPayload current [Serialized current [3]] @?= Right (Just [3])
        ]
  where
    stale = StaleAnnotationUnit (tyConPackage (typeRepTyCon current)) (tyConPackage (typeRepTyCon old))
