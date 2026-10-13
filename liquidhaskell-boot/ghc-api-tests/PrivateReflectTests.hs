{-# LANGUAGE OverloadedStrings #-}

module PrivateReflectTests (tests) where

import GHC.Types.Name (Name, mkExternalName)
import GHC.Types.Name.Occurrence (mkVarOcc)
import GHC.Types.SrcLoc (noSrcSpan)
import GHC.Types.Unique (mkUnique)
import GHC.Unit.Module (mkModule, mkModuleName)
import GHC.Unit.Types (stringToUnit)
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Bare.Axiom (resolvePrivateReflect)
import Language.Haskell.Liquid.GHC.Misc ()
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase)

tests :: TestTree
tests =
    testGroup
        "private reflection source lookup"
        [ check "authored spelling selects actual dependency" (resolvePrivateReflect spelling [actual] == Right (Just actual))
        , check "duplicate observations retain one actual identity" (resolvePrivateReflect spelling [actual, actual] == Right (Just actual))
        , check "selected dependency retains canonical unit identity" (fmap (fmap F.symbol) (resolvePrivateReflect spelling [actual]) == Right (Just (F.symbol actual)) && F.symbol actual /= spelling)
        , check "undiscovered helper is not manufactured" (resolvePrivateReflect spelling ([] :: [Name]) == Right Nothing)
        , check "different occurrence is not selected" (resolvePrivateReflect "Data.Aeson.Key.fromText1" [actual] == Right Nothing)
        , check "same spelling in distinct units rejects" (ambiguous [actual, other])
        , check "unit ambiguity is independent of discovery order" (ambiguous [other, actual])
        , check "canonical unit identities remain distinct" (F.symbol actual /= F.symbol other)
        ]
  where
    check label succeeded = testCase label (assertBool label succeeded)
    spelling = "Data.Aeson.Key.toText1"
    actual = named 'a' "aeson-actual-a"
    other = named 'b' "aeson-actual-b"
    named tag unit = mkExternalName (mkUnique tag 1) (mkModule (stringToUnit unit) (mkModuleName "Data.Aeson.Key")) (mkVarOcc "toText1") noSrcSpan
    ambiguous candidates = case resolvePrivateReflect spelling candidates of
        Left found -> length found == 2
        Right _ -> False
