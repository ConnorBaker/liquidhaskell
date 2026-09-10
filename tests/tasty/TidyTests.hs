{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}

-- | The two tidying pipelines for a 'SpecType' differ in exactly one thing:
--   whether a conjunct mentioning a data constructor test (@is$Con@) survives.
--   An error message keeps it (#2650: a user predicate over an @inline@d
--   function expands to one, and the message used to show only the base
--   type); an annotation drops it. Both directions are pinned here.
module TidyTests (tidyTests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertBool, (@?=))
import Language.Fixpoint.Types
  ( Expr, pattern PAnd, pattern PAtom, pattern EApp, pattern EVar, pattern ECon
  , pattern Reft, Brel (..), Constant (..), Tidy (..)
  , conjuncts, reftPred, syms, isPrefixOfSym )
import qualified Language.Haskell.Liquid.GHC.Misc as GM
import Language.Haskell.Liquid.Types.RType
import Language.Haskell.Liquid.Types.RTypeOp (rTypeReft)
import Language.Haskell.Liquid.UX.Tidy (tidySpecType, tidyAnnotSpecType)

-- | @{v : a | 0 < v && is$T.Con v}@: a user-written bound beside the
--   constructor test an @inline@d function expands to.
subject :: SpecType
subject = withReft [bound, test]

-- | The same type with the bound alone: the control, so that "the test
--   conjunct is gone" is distinguishable from "the refinement is gone".
control :: SpecType
control = withReft [bound]

withReft :: [Expr] -> SpecType
withReft ps = RVar (RTV (GM.stringTyVar "a")) (MkUReft (Reft ("v", PAnd ps)) mempty)

bound, test :: Expr
bound = PAtom Lt (ECon (I 0)) (EVar "v")
test  = EApp (EVar "is$T.Con") (EVar "v")

conjunctsOf :: SpecType -> [Expr]
conjunctsOf = conjuncts . reftPred . rTypeReft

mentionsTest :: Expr -> Bool
mentionsTest = any ("is$" `isPrefixOfSym`) . syms

tidyTests :: [TestTree]
tidyTests =
  [ testGroup "tidySpecType (error messages) keeps a constructor test, #2650"
      [ testCase "Lossy" $ do
          let cs = conjunctsOf (tidySpecType Lossy subject)
          length cs @?= 2
          assertBool "the is$ conjunct must survive" (any mentionsTest cs)
      , testCase "Full" $ do
          let cs = conjunctsOf (tidySpecType Full subject)
          length cs @?= 2
          assertBool "the is$ conjunct must survive" (any mentionsTest cs)
      ]
  , testGroup "tidyAnnotSpecType (annotations) drops a constructor test and nothing else"
      [ testCase "the is$ conjunct is dropped" $
          assertBool "no conjunct may mention is$"
            (not (any mentionsTest (conjunctsOf (tidyAnnotSpecType subject))))
      , testCase "the user's bound survives beside it" $
          conjunctsOf (tidyAnnotSpecType subject) @?= [bound]
      , testCase "a type without a constructor test is untouched" $
          conjunctsOf (tidyAnnotSpecType control) @?= conjunctsOf (tidySpecType Lossy control)
      ]
  ]
