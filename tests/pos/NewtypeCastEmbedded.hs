-- | A newtype EMBEDDED into its representation's logical sort. In the logic
--   the wrap and the unwrap are both the identity on that carrier, and the
--   unwrap direction already says so ('castTy'' emits @v == coerce x@). The
--   wrap direction is typed as the constructor application
--   ('castTyNewtypeWrap'), whose @v == WrappedSet s@ is an UNINTERPRETED
--   function in the embedded sort, so once the cast rule stopped assuming the
--   expected refinement, 'wrap' could no longer establish @v == values@ while
--   'unwrap' still could. The constructor type is now met with the
--   coercion-derived one whenever the two logical sorts coincide.
--
--   Measured: SAFE (47) before the cast fix; UNSAFE (47) at 'wrap' with the
--   cast fix alone; SAFE (47) with the meet -- an identical count throughout,
--   so the obligation was always raised and only its discharge moved. Those
--   are -O0 and -O2 with `--check-derived --total-Haskell --no-annotations`;
--   under the suite's own flags (-XHaskell2010 -O0, no plugin options) the
--   module is SAFE (4) before and after.
--
--   "Before" is the library at 8b5d0881b, the last tip without 4c478a5c5 (the
--   cast rule) and bc4ff8aec (the meet); "after" is 3a67a6de4, which carries
--   both. This module was registered after that code landed, so its before
--   verdict is only measurable on 8b5d0881b.
module NewtypeCastEmbedded where

import Data.Coerce (coerce)
import Data.Set (Set)

{-@ embed WrappedSet as (Set_Set Int) @-}
newtype WrappedSet = WrappedSet (Set Int)

{-@ wrap :: values : Set Int -> {v : WrappedSet | v == values} @-}
wrap :: Set Int -> WrappedSet
wrap = WrappedSet

{-@ unwrap :: wrapped : WrappedSet -> {v : Set Int | v == wrapped} @-}
unwrap :: WrappedSet -> Set Int
unwrap = coerce

{-@ roundTrip :: values : Set Int -> {v : Set Int | v == values} @-}
roundTrip :: Set Int -> Set Int
roundTrip values = unwrap (wrap values)

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v : Int | 0 < v} @-}
nonVacuity :: Int -> Int
nonVacuity n = n - 1
