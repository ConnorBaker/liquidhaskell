{-# LANGUAGE NoImplicitPrelude #-}

module ImportedInstancePredicateResultBad where

import GHC.Types (Int)

import ImportedCarrier (Pick (..))

{-@ class Pick a where
      pick :: a -> {v:a | false}
      other :: a -> a @-}

{-@ instance Pick Int where
      assume pick :: forall <p :: Int -> Bool>. Int<p> -> Int<p> @-}

good :: Int -> Int
good value = pick value
