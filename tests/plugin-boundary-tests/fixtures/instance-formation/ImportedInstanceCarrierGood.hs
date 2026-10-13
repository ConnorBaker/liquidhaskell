module ImportedInstanceCarrierGood where

import ImportedCarrier (Pick (..))

{-@ instance Pick ({v:Int | v > 0}) where
      assume pick :: x:{v:Int | v > 0} -> {v:Int | v == x} @-}

generic :: (Pick a) => a -> a
generic = pick
{-# NOINLINE generic #-}

good :: Int
good = generic 1
