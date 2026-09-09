{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The negative companion of @tests/datacon/pos/NestedCaseProjectionSort.hs@:
-- the lifted equation @a2W (A2 c) = C.sel1 c@ is an EQUALITY, so its
-- negation must fail.
module NestedCaseProjectionSort where

import Data.Set (Set)

data W = W (Set Int)

data C = C !W

data A2 = A2 C

{-@ measure a2W @-}
a2W :: A2 -> W
a2W (A2 c) = case c of C w -> w

{-@ bad :: x:A2 -> {v:W | v /= a2W x} @-}
bad :: A2 -> W
bad (A2 (C w)) = w
