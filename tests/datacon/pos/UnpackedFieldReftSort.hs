{-# OPTIONS_GHC -O1 #-}

-- | A field whose SORT changes when GHC unpacks it keeps its refinement, by
-- being rebuilt from the component it expanded to.
--
-- @G@'s second field is a strict single-field product, so
-- @-funbox-small-strict-fields@ replaces it by the @Int@ inside. The field's
-- refinement is written at sort @W@ and the component's sort is @int@, so it
-- cannot be copied across: measured, an unconditional copy fails at the DATA
-- DECLARATION with @Illegal type specification for `G`@ and
-- @Cannot unify UnpackedFieldReftSort.W with int in expression: wOf VV@. That
-- is what the sort test in 'mkProductTy''s @keepReft@ still decides, and it is
-- why this is not simply a wider copy.
--
-- What it is instead: @{v : W | wOf v <= 10}@ becomes
-- @{v : int | wOf (W v) <= 10}@. The substitution goes under the refinement's
-- own binder and rebuilds the field from the component, so the fact stated is
-- the fact that was written.
--
-- THIS MODULE WAS A NEGATIVE TEST UNTIL 2026-09-06, pinning the refinement
-- being DROPPED -- sound, and a real optimisation-dependent difference rather
-- than a repair. The measurement that moved it is a `-O` sweep on the same
-- source: @SAFE (1)@ at @-O0@, @UNSAFE (1)@ at @-O1@ and @-O2@, at an
-- IDENTICAL constraint count, so the obligation was raised at every level and
-- only its discharge moved. A user-written bound that stops being enforced
-- because GHC unpacked a field is the damage this series exists to remove, so
-- the old expectation was pinning the defect.
--
-- The companion negative is @tests/datacon/neg/UnpackedFieldReftSort.hs@,
-- which demands MORE than the field's bound gives. Without it this module is
-- discharged just as well by a rebuild that asserts @true@, which is exactly
-- what the previous behaviour did.
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
