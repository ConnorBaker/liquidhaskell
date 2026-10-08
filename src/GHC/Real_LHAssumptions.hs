{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}

-- Reexports are necessary for LH to expose specs of type classes
module GHC.Real_LHAssumptions (Integral (..), Fractional (..), numerator, denominator) where

{-@ LIQUID "--typeclass" @-}

#include "MachDeps.h"

import GHC.Classes_LHAssumptions ()
import GHC.Num.Integer (integerFromNatural)
import GHC.Num.Integer_LHAssumptions ()
import GHC.Num.Natural (Natural)
import GHC.Num.Natural_LHAssumptions ()
import GHC.Num_LHAssumptions ()
import GHC.Real
import GHC.Types_LHAssumptions ()

{-@
// No common total domain or generic arithmetic law is established for these
// dictionary-composed operations. Their checked full arrows must come from
// their actual bodies and consumed method contracts.
assume (^) :: (Num a, Integral b) => a -> {n:b | false} -> a
assume powImpl :: (Num a, Integral b) => a -> {n:b | false} -> a
assume powImplAcc :: (Num a, Integral b) => a -> {n:b | false} -> a -> a

// fromIntegral composes the actual Integral and Num dictionaries. In
// particular, conversion to Int can wrap; it has no generic identity law.
assume fromIntegral :: (Integral a, Num b) => {x:a | false} -> b

class Num a => Fractional a where
  (/)   :: a -> {v:a | false} -> a
  recip :: {v:a | false} -> a
  fromRational :: {r:Ratio Integer | false} -> a

// These observations describe every raw Ratio constructor, not just values
// produced by (%). They impose no denominator sign or normalization invariant.
measure numerator :: Ratio a -> a
  numerator ((:%) x y) = x

measure denominator :: Ratio a -> a
  denominator ((:%) x y) = y

assume numerator :: r:Ratio a -> {v:a | v = numerator r}
assume denominator :: r:Ratio a -> {v:a | v = denominator r}

// This explicit parser declaration makes the following == occurrences source
// function applications. The = used by the native numeric graphs below stays
// logical equality. Fixity declarations are local to this module's parsing;
// they do not reinterpret a client's ordinary logical predicates.
infix 4 ==

class (Real a, Enum a) => Integral a where
  quot :: a -> {y:a | y == fromInteger 1} -> a
  rem :: a -> {y:a | y == fromInteger 1} -> a
  div :: a -> {y:a | y == fromInteger 1} -> a
  mod :: a -> {y:a | y == fromInteger 1} -> a
  quotRem :: a -> {y:a | y == fromInteger 1} -> (a, a)
  divMod :: a -> {y:a | y == fromInteger 1} -> (a, a)
  toInteger :: {x:a | x == fromInteger 0} -> Integer

// These are sufficient imported-interface requirements, not generic numeric
// laws. Explicit source applications must retain the supplied Eq/Num evidence
// in both caller contracts and dictionary-field admission requirements.
// In the actual Natural dictionary, equality to native one forces NS 1, whose
// single-word division workers admit every raw dividend; equality to native
// zero forces NS 0, which is valid for conversion into the Integer model.
// Int/Integer/Word accept these same domains and retain their larger complete
// arrows below. Other checked dictionaries must satisfy the requirements by
// ordinary full-arrow subtyping; no arithmetic or conversion result is assumed.
// Merely excluding zero was false on raw Natural: NB emptyBytes differs from
// NS 0 but its multi-limb division path raises DivideByZero. The previous
// unrestricted projection also lost its validity premise after publication.

// The actual GHC.Internal.Real Integral Int fields guard zero and quotient
// overflow. Public rem/mod special-case (-1), so minInt rem/mod (-1) is zero.
// Both pair fields are required to be defined; the runtime's (bottom, 0)
// overflow pair is not a total pair. Its endpoint is selected below from the
// same GHC target header as the Int representation and arithmetic contracts.

instance Integral Int where
  assume quot :: x:Int -> y:{v:Int | IntQuotientDomain x v} -> {v:Int | IntegralQuotient x y v}
  assume rem :: x:Int -> y:{v:Int | v /= 0} -> {v:Int | IntegralRemainder x y v}
  assume div :: x:Int -> y:{v:Int | IntQuotientDomain x v} -> {v:Int | IntegralDiv x y v}
  assume mod :: x:Int -> y:{v:Int | v /= 0} -> {v:Int | IntegralMod x y v}
  assume quotRem :: x:Int -> y:{v:Int | IntQuotientDomain x v} -> ({v:Int | IntegralQuotient x y v}, {v:Int | IntegralRemainder x y v})
  assume divMod :: x:Int -> y:{v:Int | IntQuotientDomain x v} -> ({v:Int | IntegralDiv x y v}, {v:Int | IntegralMod x y v})
  assume toInteger :: x:Int -> {v:Integer | v = x}

// The actual Integer fields use the corresponding integerQuot/Rem/Div/Mod
// workers. With the existing integer-valued representation, zero is their
// only exceptional divisor; their results do not overflow.
instance Integral Integer where
  assume quot :: x:Integer -> y:{v:Integer | v /= 0} -> {v:Integer | IntegralQuotient x y v}
  assume rem :: x:Integer -> y:{v:Integer | v /= 0} -> {v:Integer | IntegralRemainder x y v}
  assume div :: x:Integer -> y:{v:Integer | v /= 0} -> {v:Integer | IntegralDiv x y v}
  assume mod :: x:Integer -> y:{v:Integer | v /= 0} -> {v:Integer | IntegralMod x y v}
  assume quotRem :: x:Integer -> y:{v:Integer | v /= 0} -> ({v:Integer | IntegralQuotient x y v}, {v:Integer | IntegralRemainder x y v})
  assume divMod :: x:Integer -> y:{v:Integer | v /= 0} -> ({v:Integer | IntegralDiv x y v}, {v:Integer | IntegralMod x y v})
  assume toInteger :: x:Integer -> {v:Integer | v = x}

// GHC.Internal.Real's actual Word fields use unsigned word division and
// integerFromWord#. Nonzero divisors are positive and there is no quotient
// overflow; div/mod are these same native quot/rem fields, not generic laws.
instance Integral Word where
  assume quot :: x:Word -> y:{Word | y /= 0} -> {v:Word | v = x / y}
  assume rem :: x:Word -> y:{Word | y /= 0} -> {v:Word | v = x mod y}
  assume div :: x:Word -> y:{Word | y /= 0} -> {v:Word | v = x / y}
  assume mod :: x:Word -> y:{Word | y /= 0} -> {v:Word | v = x mod y}
  assume quotRem :: x:Word -> y:{Word | y /= 0} -> ({v:Word | v = x / y}, {v:Word | v = x mod y})
  assume divMod :: x:Word -> y:{Word | y /= 0} -> ({v:Word | v = x / y}, {v:Word | v = x mod y})
  assume toInteger :: x:Word -> {v:Integer | v = x}

// Natural keeps its raw ADT representation. A nonzero NS divisor admits
// arbitrary raw dividends: the single-word workers read only complete limbs.
// General (including NB) divisors require both native validity checks and
// nonzero magnitude. Canonical operands produce canonical exact results;
// invalid raw dividends receive no invented result magnitude or validity.
instance Integral Natural where
  assume quot :: x:Natural -> y:{Natural | NaturalDivisionDomain x y} -> {v:Natural | NaturalQuotient x y v}
  assume rem :: x:Natural -> y:{Natural | NaturalDivisionDomain x y} -> {v:Natural | NaturalRemainder x y v}
  assume div :: x:Natural -> y:{Natural | NaturalDivisionDomain x y} -> {v:Natural | NaturalQuotient x y v}
  assume mod :: x:Natural -> y:{Natural | NaturalDivisionDomain x y} -> {v:Natural | NaturalRemainder x y v}
  assume quotRem :: x:Natural -> y:{Natural | NaturalDivisionDomain x y} -> ({v:Natural | NaturalQuotient x y v}, {v:Natural | NaturalRemainder x y v})
  assume divMod :: x:Natural -> y:{Natural | NaturalDivisionDomain x y} -> ({v:Natural | NaturalQuotient x y v}, {v:Natural | NaturalRemainder x y v})
  assume toInteger :: x:{Natural | naturalCheck x} -> {v:Integer | v = integerFromNatural x}

// These are result predicates for the resolved Int/Integer instances, not
// unconditional definitions of possibly partial generic method selectors.
// Every mathematical divisor is positive, making the sign convention
// explicit: quot truncates towards zero; div rounds towards minus infinity.
predicate SignedQuotientDomain H X Y = Y /= 0 && (X /= -H || Y /= -1)

predicate IntegralQuotient X Y V = V = (if X >= 0 then (if Y > 0 then X / Y else -(X / (-Y))) else (if Y > 0 then -((-X) / Y) else (-X) / (-Y)))
predicate IntegralRemainder X Y V = V = (if X >= 0 then X mod (if Y > 0 then Y else -Y) else -((-X) mod (if Y > 0 then Y else -Y)))
predicate IntegralDiv X Y V = V = (if Y > 0 then X / Y else (-X) / (-Y))
predicate IntegralMod X Y V = V = (if Y > 0 then X mod Y else -((-X) mod (-Y)))

@-}

#if WORD_SIZE_IN_BITS == 32
{-@ predicate IntQuotientDomain X Y = SignedQuotientDomain 2147483648 X Y @-}
#elif WORD_SIZE_IN_BITS == 64
{-@ predicate IntQuotientDomain X Y = SignedQuotientDomain 9223372036854775808 X Y @-}
#else
#error Unsupported GHC target Int width
#endif
