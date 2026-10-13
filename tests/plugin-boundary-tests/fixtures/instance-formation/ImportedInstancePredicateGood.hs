{-# LANGUAGE NoImplicitPrelude #-}

module ImportedInstancePredicateGood where

import GHC.Types (Int)

import ImportedCarrier (Pick (..))

{-@ instance Pick Int where
      assume pick :: forall <p :: Int -> Bool>. Int<p> -> Int<p> @-}

{-@ raw :: Int -> Int @-}
raw :: Int -> Int
raw x = pick x

{-@ positive :: {v:Int | v > 0} -> {v:Int | v > 0} @-}
positive :: Int -> Int
positive x = pick x
