-- | A TRUE postcondition established through a direct newtype constructor
--   application must still verify once the cast rule stops assuming it. The
--   wrap is typed as the constructor application ('castTyNewtypeWrap'), so
--   the @{-@ data @-}@ block's selector fact @unP (P s) == s@ is what
--   discharges these obligations, not the expected type.
--
--   'insertP' is the three-branch shape in which the defect was found in
--   production: two arms return the argument and one builds a new value. Its
--   postcondition is stated so that every arm has to establish it on its own.
--
--   Measured: SAFE (48) before the fix and SAFE (48) after it, at an identical
--   count, at -O0 and -O2 with `--check-derived --total-Haskell
--   --no-annotations`; SAFE (5) on both sides under the suite's own flags
--   (-XHaskell2010 -O0, no plugin options). 'nonVacuity' fails as declared
--   on both sides.
--
--   "Before" is the library at 8b5d0881b, the last tip without 4c478a5c5 (the
--   cast rule) and bc4ff8aec (the meet); "after" is 3a67a6de4, which carries
--   both. This module was registered after that code landed, so its before
--   verdict is only measurable on 8b5d0881b.
module NewtypeCast where

import qualified Data.Set as Set

{-@ data P = P { unP :: Set.Set Int } @-}
newtype P = P { unP :: Set.Set Int }

{-@ mk :: s : Set.Set Int -> {v : P | unP v == s} @-}
mk :: Set.Set Int -> P
mk s = P s

{-@ insertP :: x : Int -> p : P
            -> {v : P | (0 <= x && x <= 100) => unP v == Set_cup (Set_sng x) (unP p)} @-}
insertP :: Int -> P -> P
insertP x p
  | x < 0 = p
  | x > 100 = p
  | otherwise = P (Set.insert x (unP p))

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v : Int | 0 < v} @-}
nonVacuity :: Int -> Int
nonVacuity n = n - 1
