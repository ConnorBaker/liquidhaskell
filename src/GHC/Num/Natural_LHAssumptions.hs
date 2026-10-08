{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}

module GHC.Num.Natural_LHAssumptions where

import GHC.Num.BigNat (bigNatCheck, bigNatSize)
import GHC.Num.Integer (integerFromNatural)
import GHC.Num.Natural (Natural (..), naturalAdd, naturalCheck, naturalEq, naturalIsZero, naturalMul, naturalNe, naturalNegate, naturalQuot, naturalQuotRem, naturalRem, naturalSignum, naturalSubThrow, naturalZero)
import GHC.Prim (ByteArray#)
import GHC.Types_LHAssumptions ()

-- Natural remains an opaque/ADT value, not an integer magnitude. These
-- equations describe the actual zero observation over EVERY NS/NB value,
-- including raw noncanonical NB payloads: NB is never structural zero.
-- No constructor is assumed valid. Numeric correspondence is conditional on
-- the existing native naturalCheck observer, leaving raw NB values admitted.
--
-- The imported-function correspondences below are explicit trusted premises
-- of GHC 9.14.1's GHC.Internal.Bignum.Natural implementation, not LH checks of
-- those imported bodies. naturalIsZero (161-163) matches the measure; zero
-- (153-154) is NS 0##; naturalEq# (245-248) uses eqWord# on NS pairs and returns
-- False on mixed tags. Its NB/NB comparison is deliberately unspecified.
-- The concrete Eq Natural fields (131-134) are precisely naturalEq/naturalNe;
-- naturalNe# uses neWord# and returns True for mixed tags (255-262).
{-@
measure naturalIsZero :: Natural -> Bool
  naturalIsZero (NS word) = (word = 0)
  naturalIsZero (NB bytes) = false

// These are observations of the raw tagged representation, not a numeric
// embedding or a claim that an arbitrary NB payload is canonical. The word
// observation is useful only under naturalIsSmall; its NB equation is a
// total, deliberately uninformative default.
measure naturalIsSmall :: Natural -> Bool
  naturalIsSmall (NS word) = true
  naturalIsSmall (NB bytes) = false

// This is the mathematical magnitude of a Word#, including its high bit.
// Int would misstate the codomain once a valid NS exceeds maxBound :: Int.
measure naturalSmallValue :: Natural -> Integer
  naturalSmallValue (NS word) = word
  naturalSmallValue (NB bytes) = 0

// The validity observer follows GHC's actual checker. These two byte-array
// observations remain uninterpreted: no arbitrary payload is assumed to
// satisfy them. Their meanings are native BigNat validity and limb count.
measure bigNatCheck :: ByteArray# -> Bool
measure bigNatSize :: ByteArray# -> Word

measure naturalCheck :: Natural -> Bool
  naturalCheck (NS word) = true
  naturalCheck (NB bytes) = bigNatCheck bytes && bigNatSize bytes > 1

// The projection into the existing Integer model is used only on validated
// Naturals. Its logical extension on invalid representations is unspecified.
// In particular, this is not an embedding and equality of raw Naturals is
// not equality of projected integers.
measure integerFromNatural :: Natural -> Integer

invariant {n:Natural | naturalCheck n => (integerFromNatural n >= 0
                    && (naturalIsZero n <=> integerFromNatural n = 0)
                    && (naturalIsSmall n => integerFromNatural n = naturalSmallValue n))}

predicate NaturalSmallDivisor N = naturalIsSmall N && naturalSmallValue N > 0
predicate NaturalDivisionDomain X Y = NaturalSmallDivisor Y || (naturalCheck X && naturalCheck Y && not (naturalIsZero Y))
predicate NaturalSmallQuotient X Y V = (naturalIsSmall X && naturalIsSmall Y) => (naturalIsSmall V && naturalSmallValue V = naturalSmallValue X / naturalSmallValue Y)
predicate NaturalSmallRemainder X Y V = (naturalIsSmall X && naturalIsSmall Y) => (naturalIsSmall V && naturalSmallValue V = naturalSmallValue X mod naturalSmallValue Y)
predicate NaturalQuotient X Y V = NaturalSmallQuotient X Y V && ((naturalCheck X && naturalCheck Y) => (naturalCheck V && integerFromNatural V = integerFromNatural X / integerFromNatural Y))
predicate NaturalRemainder X Y V = NaturalSmallRemainder X Y V && ((naturalCheck X && naturalCheck Y) => (naturalCheck V && integerFromNatural V = integerFromNatural X mod integerFromNatural Y))

// These result relations are used only with the guarded arithmetic arrows
// below and the matching actual Num Natural fields. They assert no numeric
// interpretation or validity for an arbitrary raw NB operand.
predicate NaturalSum X Y V = naturalCheck V && integerFromNatural V = integerFromNatural X + integerFromNatural Y
predicate NaturalDifference X Y V = naturalCheck V && integerFromNatural V = integerFromNatural X - integerFromNatural Y
predicate NaturalProduct X Y V = naturalCheck V && integerFromNatural V = integerFromNatural X * integerFromNatural Y
predicate NaturalSign X V = naturalCheck V && naturalIsSmall V && naturalSmallValue V = (if naturalIsZero X then 0 else 1)

// Equality exposes the exact NS/NS and mixed-tag observations. A successful
// comparison involving an NS also establishes that both values are valid NS
// representations; it does not validate either operand of an NB/NB comparison.
// The zero clauses retain the same observation for contracts stated solely
// with the structural-zero measure, without requiring a numeric embedding.
predicate NaturalEquality X Y B = (naturalIsZero Y => (B <=> naturalIsZero X)) && (naturalIsZero X => (B <=> naturalIsZero Y)) && ((naturalIsSmall X || naturalIsSmall Y) => (B <=> (naturalIsSmall X && naturalIsSmall Y && naturalCheck X && naturalCheck Y && naturalSmallValue X = naturalSmallValue Y)))

assume bigNatCheck :: bytes:ByteArray# -> {b:Bool | b <=> bigNatCheck bytes}
assume bigNatSize :: bytes:ByteArray# -> {w:Word | w = bigNatSize bytes && w >= 0}
assume naturalCheck :: n:Natural -> {b:Bool | b <=> naturalCheck n}
assume integerFromNatural :: n:{Natural | naturalCheck n}
  -> {v:Integer | v = integerFromNatural n}

// Preserve the complete curried contract: a first nonbottom raw operand
// forms a function prefix, while completing the operation requires the pair
// domain. Keeping both premises on the dependent second argument also makes
// the full arrow compatible with the common empty second-input requirement.
assume naturalAdd :: x:Natural -> y:{Natural | naturalCheck x && naturalCheck y}
  -> {v:Natural | NaturalSum x y v}
assume naturalSubThrow :: x:Natural
  -> y:{Natural | naturalCheck x && naturalCheck y && integerFromNatural y <= integerFromNatural x}
  -> {v:Natural | NaturalDifference x y v}
assume naturalMul :: x:Natural -> y:{Natural | naturalCheck x && naturalCheck y}
  -> {v:Natural | NaturalProduct x y v}
assume naturalNegate :: x:{Natural | naturalIsZero x} -> {v:Natural | naturalIsZero v && v = x}
assume naturalSignum :: x:Natural -> {v:Natural | NaturalSign x v}

assume naturalQuot :: x:Natural -> y:{Natural | NaturalDivisionDomain x y}
  -> {v:Natural | NaturalQuotient x y v}
assume naturalRem :: x:Natural -> y:{Natural | NaturalDivisionDomain x y}
  -> {v:Natural | NaturalRemainder x y v}
assume naturalQuotRem :: x:Natural -> y:{Natural | NaturalDivisionDomain x y}
  -> ({v:Natural | NaturalQuotient x y v}, {v:Natural | NaturalRemainder x y v})

assume naturalIsZero :: n:Natural -> {b:Bool | b <=> naturalIsZero n}
assume naturalZero :: {n:Natural | naturalIsZero n}
assume naturalEq :: x:Natural -> y:Natural
  -> {b:Bool | NaturalEquality x y b}
assume naturalNe :: x:Natural -> y:Natural
  -> {b:Bool | NaturalEquality x y (not b)}

instance Eq Natural where
    assume (==) :: x:Natural -> y:Natural
      -> {b:Bool | NaturalEquality x y b}
    assume (/=) :: x:Natural -> y:Natural
      -> {b:Bool | NaturalEquality x y (not b)}
@-}
