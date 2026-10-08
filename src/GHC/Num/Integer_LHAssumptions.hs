{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}

module GHC.Num.Integer_LHAssumptions () where

#include "MachDeps.h"

import GHC.Num
import GHC.Num.Integer (integerFromNatural, integerToNaturalThrow)
import GHC.Num.Natural (Natural)
import GHC.Num.Natural_LHAssumptions ()
import GHC.Prim
import GHC.Types_LHAssumptions ()

{-@
assume IS :: x:Int# -> {v: Integer | v = (x :: int) }

define IS x = (x)

embed Integer as int
@-}

-- The input denotes an Integer under this module's existing Integer model.
-- Conversion rejects negative inputs. In the native Word range it constructs
-- NS with exactly that word; otherwise it constructs NB. This is a relation
-- to the two raw Natural observations, not a magnitude axiom for NB payloads.
#if WORD_SIZE_IN_BITS == 32
{-@
predicate NaturalFromInteger X V = naturalCheck V && integerFromNatural V = X
                               && (naturalIsSmall V <=> X <= 4294967295)
                               && (naturalIsSmall V => naturalSmallValue V = X)
@-}
#elif WORD_SIZE_IN_BITS == 64
{-@
predicate NaturalFromInteger X V = naturalCheck V && integerFromNatural V = X
                               && (naturalIsSmall V <=> X <= 18446744073709551615)
                               && (naturalIsSmall V => naturalSmallValue V = X)
@-}
#else
#error Unsupported GHC target Word width
#endif

{-@
assume integerToNaturalThrow :: x:{Integer | x >= 0}
  -> {v:Natural | NaturalFromInteger x v}
@-}

-- GHC.Internal.Bignum.Integer's concrete Eq/Ord fields use integerEq/Ne,
-- integerCompare/Lt/Le/Gt/Ge, with min/max selecting by integerLe#.
-- This trusted correspondence is with the existing mathematical Integer model.
{-@
instance Eq Integer where
    assume (==) :: x:Integer -> y:Integer -> {v:Bool | v <=> x = y}
    assume (/=) :: x:Integer -> y:Integer -> {v:Bool | v <=> x != y}

instance Ord Integer where
    assume (>) :: x:Integer -> y:Integer -> {v:Bool | v <=> x > y}
    assume (>=) :: x:Integer -> y:Integer -> {v:Bool | v <=> x >= y}
    assume (<) :: x:Integer -> y:Integer -> {v:Bool | v <=> x < y}
    assume (<=) :: x:Integer -> y:Integer -> {v:Bool | v <=> x <= y}
    assume compare :: x:Integer -> y:Integer
        -> {v:Ordering | ((v = EQ) <=> x = y) &&
                         ((v = LT) <=> x < y) &&
                         ((v = GT) <=> x > y)}
    assume max :: x:Integer -> y:Integer -> {v:Integer | v = (if x <= y then y else x)}
    assume min :: x:Integer -> y:Integer -> {v:Integer | v = (if x <= y then x else y)}
@-}
