{-# LANGUAGE OverloadedStrings #-}

module SplitJudgmentTests (tests) where

import Control.Monad.State (modify, runState)
import qualified DefaultSchemaSharingTests
import qualified Language.Fixpoint.Types as F
import Language.Haskell.Liquid.Constraint.Env (lookupREnv)
import Language.Haskell.Liquid.Constraint.Init (initCGI, initEnv)
import Language.Haskell.Liquid.Constraint.Split (splitCWith, splitCheckedCWith)
import qualified Language.Haskell.Liquid.Constraint.Types as CG
import Language.Haskell.Liquid.Types.RType (PVarBV (..), RPVar, RTypeBV (..), SpecType, defRFInfo)
import Language.Haskell.Liquid.Types.RTypeOp (rTypeReft, toRSort)
import Language.Haskell.Liquid.Types.RefType (ofType, strengthen, toType, uTop)
import Language.Haskell.Liquid.Types.Specs
import Language.Haskell.Liquid.Types.Types (CheckedSpecType, logicalSpecType, ordinarySpecType)
import qualified Language.Haskell.Liquid.UX.CmdLine as CmdLine
import qualified Language.Haskell.Liquid.UX.Config as LH
import qualified Liquid.GHC.API as G
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))

tests :: (LH.Config -> TargetInfo) -> TestTree
tests emptyTarget =
    testGroup
        "shared subtype leaf judgments"
        [ testCase "callback domain reverses both endpoints" $ do
            let left = arrow "callbackLeft" (arrow "argumentLeft" false boolean) boolean
                right = arrow "callbackRight" (arrow "argumentRight" boolean false) boolean
                judgments = observe left right
            assertBool "callback input was not checked in its original orientation" $
                any (\constraint -> same (CG.lhs constraint) false && same (CG.rhs constraint) boolean) judgments
            assertBool "callback result did not reverse with its enclosing domain" $
                any (\constraint -> same (CG.lhs constraint) false && same (CG.rhs constraint) boolean && present "argumentLeft" constraint) judgments
        , testCase "result context retains the original RHS domain refinement" $ do
            let left = arrow "left" boolean boolean
                right = arrow "right" false boolean
                results = filter (present "right") (observe left right)
            length results @?= 1
            mapM_
                ( \constraint -> case lookupREnv "right" (CG.renv (CG.senv constraint)) of
                    Just domain -> assertBool "the RHS domain carrier or full predicate changed" (same domain false)
                    Nothing -> assertBool "the RHS domain owner was lost" False
                )
                results
        , testCase "dependent result action reaches the leaf under its RHS owner" $ do
            let left = arrow "left" boolean (equal "left")
                right = arrow "right" boolean (equal "right")
                results = filter (present "right") (observe left right)
            length results @?= 1
            mapM_
                ( \constraint -> do
                    assertBool "the LHS result did not transport its original owner" (same (CG.lhs constraint) (equal "right"))
                    assertBool "the RHS result predicate changed" (same (CG.rhs constraint) (equal "right"))
                )
                results
        , testCase "callback rigid evidence stays in its lexical branch" $ do
            let callback = RAllP predicate boolean
                judgments = observeOwned (arrow "left" callback boolean) (arrow "right" callback boolean)
                captured = [owner | constraint <- judgments, RAllP owner _ <- [CG.lhs constraint]]
                uncaptured = [constraint | constraint <- judgments, RApp{} <- [CG.lhs constraint]]
            length captured @?= 1
            assertBool "the callback rigid owner escaped into the ordinary result leaf" (not $ null uncaptured)
            mapM_
                ( \constraint -> case CG.lhs constraint of
                    RAllP owner _ -> assertBool "the captured rigid was not introduced in this exact Gamma" (present (pname owner) constraint && pname owner /= pname predicate)
                    _ -> pure ()
                )
                judgments
        , testCase "nested rigid introductions retain distinct lexical owners" $ do
            let quantified = RAllP predicate (RAllP predicate boolean)
                judgments = observeOwned quantified quantified
            case judgments of
                [constraint] -> case CG.lhs constraint of
                    RAllP outer (RAllP inner _) -> do
                        assertBool "nested rigid owners were collapsed" (pname outer /= pname inner)
                        assertBool "outer rigid evidence was detached from Gamma" (present (pname outer) constraint)
                        assertBool "inner rigid evidence was detached from Gamma" (present (pname inner) constraint)
                    _ -> assertBool "the full lexical rigid telescope was lost" False
                _ -> assertBool "unexpected quantified leaf count" False
        ]
  where
    boolean = ofType G.boolTy :: SpecType
    predicate :: RPVar
    predicate = PV "p" (toRSort boolean) []
    false = strengthen boolean (uTop (F.Reft (F.vv_, F.PFalse)))
    equal name = strengthen boolean (uTop (F.Reft (F.vv_, F.PIff (F.EVar F.vv_) (F.EVar name))))
    arrow name domain result = RFun name defRFInfo domain result mempty
    present name = maybe False (const True) . lookupREnv name . CG.renv . CG.senv
    same :: SpecType -> SpecType -> Bool
    same actual expected =
        G.eqType (toType False actual) (toType False expected)
            && F.shiftVV (rTypeReft actual) "controlRoot" == F.shiftVV (rTypeReft expected) "controlRoot"
    observe left right = observeWith $ \environment -> splitCWith emit False (CG.SubC environment left right)
      where
        emit :: CG.CGEnv -> SpecType -> SpecType -> CG.CG [CG.FixSubC]
        emit environment lhs rhs = do
            modify (\state -> state{CG.hsCs = CG.SubC environment lhs rhs : CG.hsCs state})
            pure []
    observeOwned left right = observeWith $ \environment -> splitCheckedCWith emit False (CG.SubC environment (logicalSpecType left) (logicalSpecType right))
      where
        emit :: [RPVar] -> CG.CGEnv -> CheckedSpecType -> CheckedSpecType -> CG.CG [CG.FixSubC]
        emit owners environment lhs rhs = do
            modify (\state -> state{CG.hsCs = CG.SubC environment (foldr RAllP (ordinarySpecType lhs) owners) (ordinarySpecType rhs) : CG.hsCs state})
            pure []
    observeWith :: (CG.CGEnv -> CG.CG [CG.FixSubC]) -> [CG.SubC]
    observeWith split =
        let cfg = CmdLine.defConfig
            initial = emptyTarget cfg
            spec = giSpec initial
            names = (gsName spec){gsTcEmbeds = F.tceInsert G.boolTyCon F.boolSort F.NoArgs mempty}
            info = initial{giSpec = spec{gsName = names}}
            (_, final) =
                runState
                    ( do
                        environment <- initEnv (DefaultSchemaSharingTests.schemas info info) [] info
                        modify (\state -> state{CG.hsCs = []})
                        split environment
                    )
                    (initCGI cfg info info)
         in reverse (CG.hsCs final)
