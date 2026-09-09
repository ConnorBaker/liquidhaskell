{-# OPTIONS_GHC -O1 #-}

-- | The companion to @NestedCaseProjection.hs@: the same nested @case@, over
-- a constructor one of whose fields changes SORT when it is unpacked. @W@
-- wraps a @Set@, so unpacking @C@ rewrites that field from sort @W@ to an
-- SMT array.
--
-- This was a NEGATIVE until the 'RepMap' commit, pinning the refusal
-- @has no selector in the logic@: a field whose sort moved lost its selector,
-- and 'altToLg' could not project through @C@'s. The selector is kept now,
-- with the equation @C.sel1 (C y) = W y@ -- a field loses its selector only
-- when that rebuild names a constructor the logic does not know
-- ('fieldSelectorDropped'), and @W@ is module-local. The lifted equation is
-- @a2W (A2 c) = C.sel1 c@: the Core body @W bx@ is rewritten to
-- @W (W.sel1 (C.sel1 c))@ and 'etaCollapse' cancels the outer @W@.
--
-- 'useW' is the claim; @tests/datacon/neg/NestedCaseProjectionSort.hs@
-- demands the negation of it. The refusal itself is still pinned, on the
-- shape that still needs it, by @tests/datacon/neg/NestedCaseProjectionUnknown.hs@.
module NestedCaseProjectionSort where

import Data.Set (Set)

data W = W (Set Int)

data C = C !W

data A2 = A2 C

{-@ measure a2W @-}
a2W :: A2 -> W
a2W (A2 c) = case c of C w -> w

{-@ useW :: x:A2 -> {v:W | v == a2W x} @-}
useW :: A2 -> W
useW (A2 (C w)) = w
