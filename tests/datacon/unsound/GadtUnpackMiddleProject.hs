{-# OPTIONS_GHC -O1 #-}
{-# LANGUAGE GADTs #-}

-- | A KNOWN UNSOUNDNESS, pinned so that its repair is visible.
--
-- This module is GREEN today and must not be. 'firstOfP' claims a component
-- of an UNCONSTRAINED field is non-negative, and 'witness' is a legal value
-- that refutes it. Measured 2026-09-09 on the same source:
-- @LIQUID: SAFE (39 constraints checked)@ at @-O1@,
-- @LIQUID: UNSAFE (39 constraints checked)@ / @Liquid Type Mismatch@ at
-- @-O0@ -- an identical count, so the obligation is raised at both levels and
-- only its discharge moves.
--
-- The mechanism is the one @tests/datacon/neg/GadtUnpackMiddle.hs@ pins from
-- the other side. On a NON-VANILLA constructor 'PredType.meetWorkWrapRep'
-- pads the wrapper spec by @workN - wrapN@ at the front and zips
-- POSITIONALLY against the worker's arguments; here the worker's are
-- @[$dShow, Int#, Int#, Int#, a]@ and the spec's @[Show a, gN, gP, gA]@, so
-- the @0 <= v@ written on @gN@ lands on the first @Int#@ of the unpacked
-- @P2@. The neg module shows the bound is MISSING where it was written; this
-- one shows it is PRESENT where it was not. A pattern match then learns
-- @0 <= (first component of gP)@, a fact nobody wrote, and discharges the
-- false claim with it. The construction direction is NOT exploitable --
-- @G (-1) (P2 0 0) x@ is caught, because the construction goes through the
-- WRAPPER, whose spec entry is correctly paired -- so this is the arm.
--
-- HOW THIS SUITE WORKS. LiquidHaskell's test harness has no way to say
-- "expected to fail and currently does not": an @--expect-error-containing@
-- that goes unmatched is itself an error, so a neg registration would fail
-- today for the wrong reason and pass tomorrow for the right one, indistinct
-- from every other neg. So @datacon-unsound@ is a suite of modules that are
-- SAFE and should not be. Its exit code is inverted in meaning: green means
-- the unsoundness is still there. When a fix lands, this module goes red in
-- this suite; the response is to move it to @tests/datacon/neg/@ with
-- @{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}@, at which
-- point it is an ordinary attribution test.
--
-- Nothing in the unpacking series touches this path: 'expandProductType' is
-- a no-op on the worker spec 'dcWorkSpecType' produces, because it is already
-- rep-shaped. The fix is a field-driven pairing in 'meetWorkWrapRep' --
-- dictionary with dictionary, then each source field with the worker
-- arguments it expands to.
module GadtUnpackMiddleProject where

data P2 = P2 !Int !Int

data G a where
  G :: Show a => !Int -> {-# UNPACK #-} !P2 -> a -> G a

{-@ data G a where
      G :: Show a => gN:{v:Int | 0 <= v} -> gP:P2 -> gA:a -> G a @-}

-- FALSE: gP's first component is unconstrained; see 'witness'.
{-@ firstOfP :: G a -> {v:Int | 0 <= v} @-}
firstOfP :: G a -> Int
firstOfP (G _ (P2 a _) _) = a

-- A legal value on which 'firstOfP' returns @-1@.
witness :: G ()
witness = G 5 (P2 (-1) 0) ()
