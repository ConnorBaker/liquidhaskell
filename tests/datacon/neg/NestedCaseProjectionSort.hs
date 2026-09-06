{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=has no selector in the logic" @-}

-- | The companion to @tests/datacon/pos/NestedCaseProjection.hs@: the same
-- nested @case@, over a constructor one of whose fields changes SORT when it is
-- unpacked.
--
-- @W@ wraps a @Set@, so unpacking @C@ rewrites that field from sort @W@ to an
-- SMT array. A field selector is declared at the field's SOURCE type, so there
-- is no selector for this one in the logic -- 'makeMeasureSelectors' drops it,
-- which is what @tests/datacon/pos/UnpackedFieldSorts.hs@ pins.
--
-- 'altToLg' therefore cannot build the projection, and the question this module
-- answers is what it should do about that. 'makeDataConSelector' still HANDS IT
-- a name; using it lifts the equation around a symbol nobody declared, and the
-- failure surfaces as @Unbound symbol@ reported at the DATA DECLARATION, naming
-- neither the measure that wanted it nor the field that lost it.
--
-- The expectation pinned here is the refusal instead: named field, named
-- constructor, reported at the measure that asked.
--
-- Two things about the shape, both of which cost an arm:
--
-- * @A2@'s field is LAZY. Unpacked, the OUTER equation's own alternative is
--   rewritten by 'unpackedFieldSubst' -- a different function, which this
--   change does not touch -- and the module fails there with @Unbound symbol@
--   before 'altToLg' is ever reached. That path has the same gap and is left
--   for its own commit.
--
-- * The nested @case@ scrutinises a FIELD, not the equation's own binder.
--   @f p = case p of C w -> w@ compiles to a plain selector and never reaches
--   'altToLg' at all: measured, that spelling is @SAFE (0 constraints
--   checked)@ and pins nothing.
--
-- @--expect-error-containing@ rather than @--expect-any-error@ deliberately:
-- this module failed before the change too, so the weaker form is discharged by
-- the very defect the message exists to replace, and would pass while proving
-- nothing.
module NestedCaseProjectionSort where

import Data.Set (Set)

data W = W (Set Int)

data C = C !W

data A2 = A2 C

{-@ measure a2W @-}
a2W :: A2 -> W
a2W (A2 c) = case c of C w -> w
