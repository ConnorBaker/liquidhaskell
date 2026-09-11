-- | An UNSPECIFIED nullary binder whose body is a newtype constructor
--   application, as a PRIVATE top-level constant read by an exported consumer.
--   Its result type is a template KVar @k@ checked against itself; with the
--   expected refinement conjoined onto the cast's type the only lower bound on
--   @k@ was the tautology @k => k@, the solver took @k = false@, and every
--   binding that could see 'emptyN' was discharged by ex falso -- including
--   'nonVacuity', which is declared to fail. 'emptyN' is deliberately not
--   exported: an exported binder is the workaround users reached for.
--
--   This is the shape that pins 4c478a5c5 on the tree it lands on. The
--   instance-method form of the same constant ('NewtypeCastNullary') stopped
--   being vacuous through a different commit and is kept only as a guard.
--
--   Measured, suite flags (-XHaskell2010 -O0, no plugin options): UNSAFE (3)
--   with "declared to fail is safe" and a `Found false` at 'emptyN' on
--   8b5d0881b, and again on 3a67a6de4 with 4c478a5c5's hunk reverted; SAFE (3)
--   on 3a67a6de4, 'nonVacuity' failing as declared. At -O0 and -O2 with
--   `--check-derived --total-Haskell --no-annotations`: UNSAFE (46) with the
--   `Found false` on 8b5d0881b, SAFE (46) on 3a67a6de4.
module NewtypeCastNullaryPrivate (observed, nonVacuity) where

import qualified Data.Set as Set

newtype N = N (Set.Set Int)

emptyN :: N
emptyN = N Set.empty

observed :: Int
observed = case emptyN of N s -> Set.size s

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v : Int | 0 < v} @-}
nonVacuity :: Int -> Int
nonVacuity n = n - 1
