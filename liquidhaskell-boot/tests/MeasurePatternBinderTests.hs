{-# LANGUAGE OverloadedStrings #-}

module MeasurePatternBinderTests (tests) where

import Control.Monad (forM_)
import Data.List (isInfixOf, nub)
import qualified Language.Fixpoint.Types as F
import qualified Language.Haskell.Liquid.Parse as LH
import qualified Language.Haskell.Liquid.Types.Types as Measure
import Test.Tasty
import Test.Tasty.HUnit
import Text.Megaparsec.Error (errorBundlePretty)
import Text.Megaparsec.Pos (initialPos)

tests :: TestTree
tests =
    testGroup
        "measure pattern binders"
        [ testCase "constructor, list, tuple, and instance wildcards are distinct"
            $ forM_
                [ "measure keep :: Pair -> Bool\n  keep (Pair _ _) = true"
                , "measure keep :: [Int] -> Bool\n  keep (_ : _) = true"
                , "measure keep :: (Int,Int) -> Bool\n  keep (_,_) = true"
                , "instance measure keep :: Pair -> Bool\n  keep (Pair _ _) = true"
                ]
            $ \src -> do
                (names, _) <- equation src
                length names @?= 2
                length (nub names) @?= 2
                assertBool "wildcard remained a referable binder" ("_" `notElem` names)
        , testCase "fresh wildcard avoids a hostile named field and its body use" $ do
            let hostile = F.tempSymbol "measureWildcard" 1
            (names, result) <-
                equation $
                    unlines
                        [ "measure keep :: Pair -> Int"
                        , "  keep (Pair _ lq_tmp$measureWildcard##1) = lq_tmp$measureWildcard##1"
                        ]
            case names of
                [anonymous, named] -> do
                    named @?= hostile
                    anonymous @?= F.tempSymbol "measureWildcard" 2
                    fmap F.val result @?= Measure.E (F.EVar named)
                _ -> assertFailure "unexpected pattern arity"
        , testCase "fresh wildcard avoids a hostile free body name" $ do
            let hostile = F.tempSymbol "measureWildcard" 1
            (names, result) <-
                equation $
                    unlines
                        [ "measure keep :: Pair -> Int"
                        , "  keep (Pair _ _) = lq_tmp$measureWildcard##1"
                        ]
            assertBool "wildcard captured a body name" (hostile `notElem` names)
            fmap F.val result @?= Measure.E (F.EVar hostile)
        , testCase "fresh wildcard avoids an unused refinement result binder" $ do
            let hostile = F.tempSymbol "measureWildcard" 1
            (names, _) <-
                equation $
                    unlines
                        [ "measure keep :: Pair -> Int"
                        , "  keep (Pair _ _) = {lq_tmp$measureWildcard##1 | true}"
                        ]
            assertBool "wildcard captured the refinement result binder" (hostile `notElem` names)
        , testCase "a locally bound refinement underscore remains valid" $ do
            (_, result) <-
                equation $
                    unlines
                        [ "measure keep :: Pair -> Int"
                        , "  keep (Pair _ _) = {_ | _ == 0}"
                        ]
            fmap F.val result @?= Measure.R "_" (F.PAtom F.Eq (F.EVar "_") (F.ECon (F.I 0)))
        , testCase "a locally bound expression underscore remains valid" $ do
            (_, result) <- equation "measure keep :: Pair -> (Int -> Int)\n  keep (Pair _ _) = \\_:int -> _"
            fmap F.val result @?= Measure.E (F.ELam ("_", F.FInt) (F.EVar "_"))
        , testCase "duplicate named constructor, list, tuple, and instance binders reject"
            $ forM_
                [ "measure keep :: Pair -> Int\n  keep (Pair x x) = x"
                , "measure keep :: [Int] -> Int\n  keep (x : x) = 0"
                , "measure keep :: (Int,Int) -> Int\n  keep (x,x) = x"
                , "instance measure keep :: Pair -> Int\n  keep (Pair x x) = x"
                ]
            $ rejects "duplicate measure pattern binder: x"
        , testCase "underscore-prefixed names are ordinary binders" $
            rejects
                "duplicate measure pattern binder: _x"
                "measure keep :: Pair -> Int\n  keep (Pair _x _x) = _x"
        , testCase "free underscore rejects even without an anonymous field" $
            rejects
                "anonymous measure pattern wildcard '_' cannot be used in the body"
                "measure keep :: Pair -> Int\n  keep (Pair x y) = _"
        , testCase "anonymous wildcard cannot be read in the body" $
            rejects
                "anonymous measure pattern wildcard '_' cannot be used in the body"
                "measure keep :: Pair -> Int\n  keep (Pair _ x) = _"
        ]
  where
    equation src = case LH.singleSpecP (initialPos "<test>") src of
        Right (LH.Meas m) -> onlyEquation (Measure.msEqns m)
        Right (LH.IMeas m) -> onlyEquation (Measure.msEqns m)
        Right _ -> assertFailure "expected a measure" >> fail "expected a measure"
        Left err -> assertFailure (errorBundlePretty err) >> fail "measure did not parse"
    onlyEquation [d] = return (map fst (Measure.binds d), Measure.body d)
    onlyEquation _ = assertFailure "expected one equation" >> fail "expected one equation"
    rejects message src = case LH.singleSpecP (initialPos "<test>") src of
        Left err -> assertBool (errorBundlePretty err) (message `isInfixOf` errorBundlePretty err)
        Right _ -> assertFailure "invalid measure binders were accepted"
