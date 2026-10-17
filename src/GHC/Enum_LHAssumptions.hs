{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}

module GHC.Enum_LHAssumptions where

import GHC.Classes_LHAssumptions ()
import GHC.Internal.Enum (enumIntToWord)
import GHC.Num_LHAssumptions ()

-- GHC's derived Enum and Ix instances decode tags through a generated
-- $tag2con helper whose body is tagToEnum#. That helper has no declared
-- domain: its parameter is inferred from the generated callers, which
-- --check-derived checks like any other binding. The callers obtain their
-- tag ranges from the operations below, so these are the facts that range
-- inference needs; tagToEnum# keeps its own [0, constructor count) domain.
--
-- Each arrow describes only the resolved Int instance or function in
-- ghc-internal-9.1401.0, src/GHC/Internal/Enum.hs:
--
-- * enumFromTo (I# x) (I# y) = eftInt x y (line 591). eftInt (line 620)
--   returns [] when x > y and otherwise counts up from x, stopping at y,
--   so every element lies in [lo, hi].
-- * enumFromThenTo (I# x1) (I# x2) (I# y) = efdtInt x1 x2 y (line 599).
--   efdtInt selects efdtIntUp when x2 >= x1 and efdtIntDn otherwise.
--   efdtIntUp (line 674) yields x1 and then steps that stay at most y;
--   efdtIntDn (line 705) yields x1 and then steps that stay at least y.
--   Every element therefore lies between x1 and y, in either order. The
--   element order and step are not stated.
-- * enumIntToWord (I# i) = W# (int2Word# i) (line 1098): the same bits read
--   as an unsigned machine word, i.e. the argument modulo 2^WORD_SIZE.
--
-- An unknown Enum dictionary acquires none of these contracts.
{-@
instance Enum Int where
    assume enumFromTo :: lo:Int -> hi:Int -> [{v:Int | lo <= v && v <= hi}]
    assume enumFromThenTo :: x1:Int -> x2:Int -> y:Int -> [{v:Int | (x1 <= v && v <= y) || (y <= v && v <= x1)}]

assume GHC.Internal.Enum.enumIntToWord :: x:Int -> {v:Word | WordWrap x v}
@-}
