{-# OPTIONS_GHC -O1 #-}

-- | The 'unpackedFieldSubst' twin of @NestedCaseProjectionSort.hs@: a lifted
-- equation whose OWN top-level alternative -- not a nested @case@ -- projects
-- through a field whose sort moved. @A2@'s field is STRICT, so GHC unpacks
-- @C@, and through it @W@, and @A2@'s worker takes the @Set@.
--
-- This was a NEGATIVE until the 'RepMap' commit, pinning the refusal
-- @has no selector in the logic@. @C@'s selector is kept now, with the
-- equation @C.sel1 (C y) = W y@, so the projection is
-- @bx := W.sel1 (C.sel1 c)@ and the Core body @C bx@ becomes
-- @C (W.sel1 (C.sel1 c))@ -- @C@ applied to its one LEAF projection, which
-- 'etaCollapse' cancels to @c@. The equation is @a2C (A2 c) = c@, and over
-- the worker @a2C (A2 y) = C y@.
--
-- 'useA2' is the claim; @tests/datacon/neg/UnpackedFieldSubstSort.hs@
-- demands its negation, and @tests/datacon/neg/UnpackedFieldSubstUnknown.hs@
-- pins the refusal on the shape that still needs it.
module UnpackedFieldSubstSort where

import Data.Set (Set)

data W = W (Set Int)

data C = C !W

data A2 = A2 !C

{-@ measure a2C @-}
a2C :: A2 -> C
a2C (A2 c) = c

{-@ useA2 :: x:A2 -> {v:C | v == a2C x} @-}
useA2 :: A2 -> C
useA2 (A2 c) = c
