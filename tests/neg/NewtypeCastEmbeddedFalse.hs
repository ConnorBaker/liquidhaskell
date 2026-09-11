{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | GUARD for the meet in 'castTyNewtypeWrap': the identity it adds for an
--   embedded newtype is @v == values@, derived from the coercion, and it must
--   not be able to prove the opposite. Red before the fix? NO -- before the
--   fix this module was SAFE, because the expected refinement @v /= values@
--   was conjoined onto the cast's type like any other. So this module pins
--   both halves: the false contract is caught, and the meet does not
--   re-open the hole it closes.
--
--   Measured: SAFE (1) before the fix (contract discharged for free),
--   UNSAFE (1) with the cast fix alone and UNSAFE (1) with the meet, at -O0
--   and -O2 with `--check-derived --total-Haskell --no-annotations`; SAFE (1)
--   before and UNSAFE (1) after under the suite's own flags (-XHaskell2010
--   -O0, no plugin options).
--
--   "Before" is the library at 8b5d0881b, the last tip without 4c478a5c5 (the
--   cast rule) and bc4ff8aec (the meet); "after" is 3a67a6de4, which carries
--   both. This module was registered after that code landed, so its before
--   verdict is only measurable on 8b5d0881b.
module NewtypeCastEmbeddedFalse where

import Data.Set (Set)

{-@ embed WrappedSet as (Set_Set Int) @-}
newtype WrappedSet = WrappedSet (Set Int)

{-@ forged :: values : Set Int -> {v : WrappedSet | v /= values} @-}
forged :: Set Int -> WrappedSet
forged = WrappedSet
