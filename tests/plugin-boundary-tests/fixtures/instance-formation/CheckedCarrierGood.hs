module CheckedCarrierGood where

import CheckedCarrier

generic :: (Pick a) => a -> a
generic = pick
{-# NOINLINE generic #-}

good :: Int
good = generic 1
