-- | GUARD. The same unspecified newtype constant as
--   'NewtypeCastNullaryPrivate', but as an INSTANCE METHOD:
--   @mempty = N Set.empty@ of a hand-written 'Monoid' instance, the shape
--   @deriving via@ generates for a newtype over 'Set.Set'. Before the cast
--   fix this module was vacuous: @mempty@'s template KVar had only @k => k@
--   as a lower bound, solved to @false@, and 'nonVacuity' -- declared to
--   fail -- verified.
--
--   What it does and does not pin. On the tree right after 4c478a5c5 the
--   module flips exactly as the private shape does (UNSAFE (3) "declared to
--   fail is safe" on 8b5d0881b, SAFE (1) at 4c478a5c5, suite flags). On the
--   tree it lands on it does NOT pin the cast rule: with 4c478a5c5's hunk
--   reverted on 3a67a6de4 it stays SAFE (1), because f02299a89 ("Check
--   instance methods against their dictionary-promised domains") types an
--   instance method against its class-promised type and the poisonable KVar
--   is no longer there. It stays registered as a guard that an instance
--   method built by direct newtype construction leaves the module
--   non-vacuous; 'NewtypeCastNullaryPrivate' is the pin.
--
--   Measured, suite flags (-XHaskell2010 -O0, no plugin options): UNSAFE (3)
--   at the `fail` pragma (44:10 in this file) before, SAFE (1) after; the
--   verdicts were taken on a bisect-panel copy with a nine-line-shorter
--   header and an identical body, which reported the site as 32:10. At -O0
--   and -O2 with `--check-derived
--   --total-Haskell --no-annotations`: UNSAFE (756) with `Found false` at
--   'mempty' before, SAFE (399) after.
--
--   "Before" is the library at 8b5d0881b, the last tip without 4c478a5c5 (the
--   cast rule) and bc4ff8aec (the meet); "after" is 3a67a6de4, which carries
--   both. This module was registered after that code landed, so its before
--   verdict is only measurable on 8b5d0881b.
module NewtypeCastNullary where

import qualified Data.Set as Set

newtype N = N (Set.Set Int)

instance Semigroup N where
  N a <> N b = N (Set.union a b)

instance Monoid N where
  mempty = N Set.empty

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v : Int | 0 < v} @-}
nonVacuity :: Int -> Int
nonVacuity n = n - 1
