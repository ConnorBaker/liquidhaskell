{-# LANGUAGE OverloadedStrings #-}

module SpecClosureTests (tests) where

import Data.Either (isLeft, isRight)
import Data.List (sort)
import qualified GHC.Unit.Module as GHC
import qualified GHC.Unit.Types as GHC
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Bare.Check (checkBareSpec)
import qualified Language.Haskell.Liquid.Types.DataDecl as D
import Language.Haskell.Liquid.Types.Names
import Language.Haskell.Liquid.Types.RType (RTypeBV (RHole), ofReft)
import Language.Haskell.Liquid.Types.Specs
import Language.Haskell.Liquid.Types.Types (MeasureKind (MsChecker, MsMeasure, MsSelector), MeasureV (..))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

tests :: TestTree
tests =
    testGroup
        "exported measure closure"
        [ testCase "generated names retain their complete identity" $ do
            let names = map makeGeneratedLogicLHName ["is$A.Box", "is$B.Box"]
            exportedNames MsChecker names @?= sort names
        , testCase "native datatype selectors retain their complete identity" $ do
            -- These names are produced by makeDataDecls / dataConMap for two
            -- source modules declaring data Box = Box Int.
            -- Textual module stripping collapses both to Box##1, unlike
            -- is$-prefixed checkers, which already survive that operation.
            let names =
                    map
                        makeGeneratedLogicLHName
                        [ "HiddenLeft.Box##lqdc##$select##HiddenLeft.Box##1"
                        , "HiddenRight.Box##lqdc##$select##HiddenRight.Box##1"
                        ]
            exportedNames MsSelector names @?= sort names
        , testCase "ordinary measures retain last short-name precedence" $ do
            let a = ordinary "A"
                b = ordinary "B"
            exportedNames MsMeasure [a, b] @?= [b]
            exportedNames MsMeasure [b, a] @?= [a]
        , testCase "generated selector is the definition of its resolved field" $
            isRight (checkBareSpec (fieldSpec [(fieldName, MsSelector)])) @?= True
        , testCase "authored measure cannot redeclare a data field" $
            isLeft (checkBareSpec (fieldSpec [(fieldName, MsMeasure)])) @?= True
        , testCase "same spelling with another resolved origin is not the field" $
            isLeft (checkBareSpec (fieldSpec [(ordinary "Other", MsSelector)])) @?= True
        , testCase "checker provenance does not excuse a field collision" $
            isLeft (checkBareSpec (fieldSpec [(fieldName, MsChecker)])) @?= True
        , testCase "duplicate generated measures are still rejected" $
            isLeft (checkBareSpec (fieldSpec [(fieldName, MsSelector), (fieldName, MsSelector)])) @?= True
        ]

ordinary :: String -> LHName
ordinary m =
    LHNResolved
        (LHRLogic $ LogicName "value" (GHC.mkModule GHC.mainUnit $ GHC.mkModuleName m) Nothing)
        "value"

fieldName :: LHName
fieldName = ordinary "Definition"

-- This tests raw declaration-category validation, before GHC name lookup and
-- measure type checking. Generated provenance is assigned by the producer;
-- authored measure syntax assigns MsMeasure, not MsSelector.
fieldSpec :: [(LHName, MeasureKind)] -> BareSpec
fieldSpec namedKinds = mempty{dataDecls = [declaration], measures = map measure namedKinds}
  where
    fieldType = RHole $ ofReft F.trueReft
    declaration =
        D.DataDecl
            { D.tycName = D.DnName $ F.dummyLoc $ makeLocalLHName "Box"
            , D.tycTyVars = []
            , D.tycPVars = []
            , D.tycDCons = Just [D.DataCtor (F.dummyLoc $ makeLocalLHName "Box") [] [] [(fieldName, fieldType)] Nothing]
            , D.tycSrcPos = F.dummyPos "field declaration"
            , D.tycSFun = Nothing
            , D.tycPropTy = Nothing
            , D.tycKind = D.DataUser
            }
    measure (name, kind) =
        M
            { msName = F.dummyLoc name
            , msSort = F.dummyLoc fieldType
            , msEqns = []
            , msKind = kind
            , msUnSorted = []
            }

exportedNames :: MeasureKind -> [LHName] -> [LHName]
exportedNames kind names =
    sort $ map (F.val . msName) $ measures $ unsafeFromLiftedSpec $ toLiftedSpec spec
  where
    spec :: BareSpecLHName
    spec = mempty{measures = map measure names}
    measure name =
        M
            { msName = F.dummyLoc name
            , msSort = F.dummyLoc $ RHole $ ofReft F.trueReft
            , msEqns = []
            , msKind = kind
            , msUnSorted = []
            }
