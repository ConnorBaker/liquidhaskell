module ImportedInstanceCarrierGenericBad where

import ImportedCarrier (Pick (..))

{-@ instance Pick ({v:Int | v > 0}) where
      assume pick :: x:{v:Int | v > 0} -> {v:Int | v == x} @-}

generic :: (Pick a) => a -> a
generic = pick
{-# NOINLINE generic #-}

bad :: Int
bad = generic 0
