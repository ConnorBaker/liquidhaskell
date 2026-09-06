{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The SORT guard on @mkProductTy@'s refinement transfer, and the reason it
-- is a guard rather than an unconditional copy.
--
-- 'G''s second field is a strict single-field product, so unpacking replaces
-- it by the @Int@ inside -- and then by @Int#@. The field's refinement is
-- written at sort @W@; the component's sort is @int@. Copying it across
-- unconditionally is not merely imprecise, it is ill-sorted: measured, this
-- module then fails at the DATA DECLARATION with
-- @Illegal type specification for `G`@ and
-- @Cannot unify UnpackedFieldReftSort.W with int in expression: wOf VV@,
-- which is the same shape @tests/datacon/pos/UnpackedFieldSorts.hs@ exists to
-- keep out.
--
-- So this is a NEGATIVE test whose expectation is the WEAKER failure. With the
-- guard the declaration is accepted, @wOf@'s bound is simply absent from the
-- logic for this field, and 'useG' fails as an ordinary
-- @Liquid Type Mismatch@ at the consumer. That is the same cost
-- @UnpackedFieldSorts@ records in its own header -- a field whose sort changes
-- under unpacking cannot be named in the logic -- and it is the sound
-- direction: nothing that was unprovable becomes provable.
--
-- @--expect-error-containing@, not @--expect-any-error@: without the guard
-- this module ALSO fails, and the weaker form would be discharged by the very
-- defect the guard exists to prevent.
module UnpackedFieldReftSort where

data W = W Int

{-@ measure wOf @-}
wOf :: W -> Int
wOf (W n) = n

{-@ data G = G [Int] {v : W | wOf v <= 10} @-}
data G = G ![Int] !W

{-@ needSmall :: {v : W | wOf v <= 10} -> Int @-}
needSmall :: W -> Int
needSmall (W n) = n

useG :: G -> Int
useG (G _ w) = needSmall w
