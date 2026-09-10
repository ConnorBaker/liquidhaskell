{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The negative half of @tests/datacon/pos/UnpackedFieldSum.hs@: the same
-- record, with a claim the measure equation contradicts -- 'bad' returns
-- @dN d@ and claims @v /= dN d@. Pins that the positive's @SAFE@ is a proof
-- about 'dN' and not a vacuous environment: dropping the unpacked sum field's
-- selector took nothing else with it. @UNSAFE (1 constraints checked)@ with
-- the fix.
--
-- A GUARD with respect to the series, NOT an attribution: against the series
-- tip this module is rejected with @Illegal type specification for `D`@, and
-- against the series base with @Specified type does not refine Haskell type@,
-- and neither text matches @Liquid Type Mismatch@ -- so before the fix it FAILS
-- as a negative (exit 1, no verdict) rather than being discharged by the wrong
-- error. That is why the filter is @--expect-error-containing@ and not
-- @--expect-any-error@, which the defect itself would satisfy.
module UnpackedFieldSum where

data D = D { dM :: {-# UNPACK #-} !(Maybe Int), dN :: !Int }

{-@ measure dN @-}

{-@ bad :: d:D -> {v:Int | v /= dN d} @-}
bad :: D -> Int
bad (D _ n) = n
