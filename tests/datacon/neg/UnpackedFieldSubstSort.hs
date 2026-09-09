{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The negative companion of @tests/datacon/pos/UnpackedFieldSubstSort.hs@:
-- the collapsed equation @a2C (A2 c) = c@ is an EQUALITY, so its negation
-- must fail.
module UnpackedFieldSubstSort where

import Data.Set (Set)

data W = W (Set Int)

data C = C !W

data A2 = A2 !C

{-@ measure a2C @-}
a2C :: A2 -> C
a2C (A2 c) = c

{-@ bad :: x:A2 -> {v:C | v /= a2C x} @-}
bad :: A2 -> C
bad (A2 c) = c
