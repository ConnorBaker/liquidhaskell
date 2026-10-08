{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}

module GHC.Num_LHAssumptions (Num (..)) where

#include "MachDeps.h"

import GHC.Num
import GHC.Num.Integer_LHAssumptions ()
import GHC.Num.Natural (Natural)

-- A Num dictionary supplies operations, not mathematical arithmetic laws.
-- Machine Int contracts and actual primitive interpretation use the GHC
-- target's signed modular arithmetic. Other carriers do not
-- inherit integer or real arithmetic merely by having a Num instance.
--
-- Integer's concrete dictionary below is an explicit trusted correspondence
-- with GHC.Internal.Num: its fields call integerAdd/Sub/Mul/Negate/Abs/Signum,
-- and its fromInteger field is the identity. No machine overflow is involved.
--
-- These are required common interface contracts, not laws inferred from Num.
-- Unknown binary arithmetic and negation have no usable common domain here;
-- stronger concrete instance contracts below retain their actual domains.
-- Consuming a class contract requires checking or explicitly trusting every
-- corresponding method implementation. In particular, a Num label alone
-- does not establish termination even for nonnegative fromInteger inputs.
{-@
class Num a where
    (+)         :: a -> {y:a | false} -> a
    (-)         :: a -> {y:a | false} -> a
    (*)         :: a -> {y:a | false} -> a
    negate      :: {x:a | false} -> a
    abs         :: a -> a
    signum      :: a -> a
    fromInteger :: {x:Integer | x >= 0} -> a

instance Num Integer where
    assume (+) :: x:Integer -> y:Integer -> {v:Integer | v = x + y}
    assume (-) :: x:Integer -> y:Integer -> {v:Integer | v = x - y}
    assume (*) :: x:Integer -> y:Integer -> {v:Integer | v = x * y}
    assume negate :: x:Integer -> {v:Integer | v = -x}
    assume abs :: x:Integer -> {v:Integer | v = (if x >= 0 then x else -x)}
    assume signum :: x:Integer -> {v:Integer | v = (if x > 0 then 1 else (if x < 0 then -1 else 0))}
    assume fromInteger :: x:Integer -> {v:Integer | v = x}
@-}

-- The common conversion domain includes Natural, whose actual field raises
-- underflow on negative integers. Other checked dictionaries must accept this
-- domain by ordinary instance/class subtyping; their class name supplies no
-- arithmetic result law. Known Integer/Int/Word dictionaries keep their larger
-- domains in the instance-specific contracts, including negative conversions.

-- GHC.Internal.Num's actual Num Natural field is integerToNaturalThrow.
-- Reuse that worker's complete partial arrow, not only its function identity:
-- dictionary selection must preserve validity and projected magnitude even
-- when fromInteger is passed as a value before its Integer argument is known.
-- This is an instance-specific correspondence, not a law of arbitrary Num.
{-@
instance Num Natural where
    assume (+) :: x:Natural -> y:{Natural | naturalCheck x && naturalCheck y}
      -> {v:Natural | NaturalSum x y v}
    assume (-) :: x:Natural
      -> y:{Natural | naturalCheck x && naturalCheck y && integerFromNatural y <= integerFromNatural x}
      -> {v:Natural | NaturalDifference x y v}
    assume (*) :: x:Natural -> y:{Natural | naturalCheck x && naturalCheck y}
      -> {v:Natural | NaturalProduct x y v}
    assume negate :: x:{Natural | naturalIsZero x} -> {v:Natural | naturalIsZero v && v = x}
    assume abs :: x:Natural -> {v:Natural | v = x}
    assume signum :: x:Natural -> {v:Natural | NaturalSign x v}
    assume fromInteger :: x:{Integer | x >= 0} -> {v:Natural | NaturalFromInteger x v}
@-}

-- One mathematical wrap operation describes each machine carrier. The
-- concrete dictionary, not a Num constraint, supplies its modulus and sign.
{-@
predicate UnsignedWrap M X V = V = X mod M
predicate SignedWrap H X V = V = ((X + H) mod (2 * H)) - H
@-}

-- These contracts belong only to the resolved native Num Int/Word dictionaries.
-- They preserve the same meaning when a method is passed or partially applied;
-- an unknown dictionary argument must not acquire either instance's contract.
-- Word's methods belong here with GHC.Internal.Num, not GHC.Internal.Word:
-- their complete arrows must be available even to Prelude-only clients.
#if WORD_SIZE_IN_BITS == 32
{-@ predicate IntWrap X V = SignedWrap 2147483648 X V @-}
{-@ predicate WordWrap X V = UnsignedWrap 4294967296 X V @-}
#elif WORD_SIZE_IN_BITS == 64
{-@ predicate IntWrap X V = SignedWrap 9223372036854775808 X V @-}
{-@ predicate WordWrap X V = UnsignedWrap 18446744073709551616 X V @-}
#else
#error Unsupported GHC target Int/Word width
#endif
{-@
instance Num Int where
    assume (+) :: x:Int -> y:Int -> {v:Int | IntWrap (x + y) v}
    assume (-) :: x:Int -> y:Int -> {v:Int | IntWrap (x - y) v}
    assume (*) :: x:Int -> y:Int -> {v:Int | IntWrap (x * y) v}
    assume negate :: x:Int -> {v:Int | IntWrap (-x) v}
    assume abs :: x:Int -> {v:Int | IntWrap (if x >= 0 then x else -x) v}
    assume signum :: x:Int -> {v:Int | v = (if x > 0 then 1 else (if x < 0 then -1 else 0))}
    assume fromInteger :: x:Integer -> {v:Int | IntWrap x v}

instance Num Word where
    assume (+) :: x:Word -> y:Word -> {v:Word | WordWrap (x + y) v}
    assume (-) :: x:Word -> y:Word -> {v:Word | WordWrap (x - y) v}
    assume (*) :: x:Word -> y:Word -> {v:Word | WordWrap (x * y) v}
    assume negate :: x:Word -> {v:Word | WordWrap (-x) v}
    assume abs :: x:Word -> {v:Word | v = x}
    assume signum :: x:Word -> {v:Word | v = (if x = 0 then 0 else 1)}
    assume fromInteger :: x:Integer -> {v:Word | WordWrap x v}
@-}
