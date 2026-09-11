{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The nullary form of 'NewtypeCastFalse': a top-level constant built by
--   applying a newtype constructor directly. This is the shape of a
--   hand-written @mempty = N Set.empty@, and of the @mempty@ / aeson
--   @omittedField@ bodies that @deriving via@ generates, under an explicit
--   contract. With the expected refinement conjoined onto the cast's type the
--   false contract was discharged for free.
--
--   Measured: SAFE (1) before the fix, UNSAFE (1) after it, identically at -O0
--   and -O2 with `--check-derived --total-Haskell --no-annotations` and under
--   the suite's own flags (-XHaskell2010 -O0, no plugin options).
--
--   "Before" is the library at 8b5d0881b, the last tip without 4c478a5c5 (the
--   cast rule) and bc4ff8aec (the meet); "after" is 3a67a6de4, which carries
--   both. This module was registered after that code landed, so its before
--   verdict is only measurable on 8b5d0881b.
module NewtypeCastNullaryFalse where

import qualified Data.Set as Set

newtype N = N (Set.Set Int)

{-@ emptyN :: {v : N | false} @-}
emptyN :: N
emptyN = N Set.empty
