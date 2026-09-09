{-# OPTIONS_GHC -O1 #-}
{-# LANGUAGE GADTs #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | A NON-VANILLA constructor -- GADT syntax with a class context -- whose
-- middle strict field is an @{-# UNPACK #-}@ed two-field product. Worker
-- value arguments: @[$dShow, Int#, Int#, Int#, a]@; the wrapper spec's:
-- @[Show a, gN, gP, gA]@.
--
-- This shape takes the path the unpacking series never touched.
-- 'PredType.dataConPSpecType' sees @isVanillaDataCon@ False and builds the
-- worker's spec with 'dcWorkSpecType', whose 'meetWorkWrapRep' pads
-- @workN - wrapN = 1@ at the FRONT and then zips POSITIONALLY. The user's
-- @0 <= v@ on @gN@ is therefore met with the FIRST @Int#@ of the unpacked
-- @P2@, one binder to the right of the field it was written on.
-- 'RefType.expandProductType' is a no-op afterwards, since the worker's type
-- is already rep-shaped, so nothing repairs the pairing.
--
-- QUIET rather than loud: every misplaced sort is @int@, so the declaration
-- is accepted and 'useG' -- provable exactly when @0 <= v@ sits on the first
-- value argument -- is @UNSAFE@ with @Liquid Type Mismatch@. The inferred
-- type in the message quotes @bx_dRc : {0 <= bx_dRc}@ on the P2 component
-- while the binder 'useG' reads is unconstrained.
--
-- A fix that pairs by FIELD rather than by position -- dictionary with
-- dictionary, then each source field with the worker arguments it expands to
-- -- makes this SAFE, and it moves to @pos@. Its soundness mirror is
-- @tests/datacon/unsound/GadtUnpackMiddleConstruct.hs@: the same mislanding
-- lets a construction that VIOLATES the written bound verify.
--
-- @-O0@ is SAFE: UNPACK is ignored and @!Int@ is not unboxed, so worker and
-- wrapper differ only by the dictionary, which the pad absorbs correctly.
module GadtUnpackMiddle where

data P2 = P2 !Int !Int

data G a where
  G :: Show a => !Int -> {-# UNPACK #-} !P2 -> a -> G a

{-@ data G a where
      G :: Show a => gN:{v:Int | 0 <= v} -> gP:P2 -> gA:a -> G a @-}

{-@ useG :: G a -> {v:Int | 0 <= v} @-}
useG :: G a -> Int
useG (G n _ _) = n

{-@ mk :: {n:Int | 0 <= n} -> a -> G a @-}
mk :: Show a => Int -> a -> G a
mk n x = G n (P2 n n) x
