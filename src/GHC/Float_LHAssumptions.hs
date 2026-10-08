{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}

module GHC.Float_LHAssumptions (Floating (..)) where

import GHC.Float
import GHC.Real (Ratio, denominator, numerator)
import GHC.Real_LHAssumptions ()

-- Floating has only Fractional as a superclass, not ordering evidence or
-- ordered-real laws. Native IEEE exp can underflow, tanh can saturate, and
-- NaN is unordered. These arrows are requirements on checked dictionaries;
-- they do not prove that arbitrary imported method implementations terminate.
{-@
class Fractional a => Floating a where
  pi       :: a
  exp      :: a -> a
  log      :: a -> a
  sqrt     :: a -> a
  (**)     :: a -> a -> a
  logBase  :: a -> a -> a
  sin      :: a -> a
  cos      :: a -> a
  tan      :: a -> a
  asin     :: a -> a
  acos     :: a -> a
  atan     :: a -> a
  sinh     :: a -> a
  cosh     :: a -> a
  tanh     :: a -> a
  asinh    :: a -> a
  acosh    :: a -> a
  atanh    :: a -> a
  log1p    :: a -> a
  expm1    :: a -> a
  log1pexp :: a -> a
  log1mexp :: a -> a

// These complete arrows belong to the actual GHC.Internal.Float dictionaries.
// IEEE arithmetic is defined also at NaN, infinity, zero and overflow; none
// of these result types asserts an exact real-arithmetic equation.
instance Num Float where
  assume (+) :: Float -> Float -> Float
  assume (-) :: Float -> Float -> Float
  assume (*) :: Float -> Float -> Float
  assume negate :: Float -> Float
  assume abs :: Float -> Float
  assume signum :: Float -> Float
  assume fromInteger :: Integer -> Float

instance Num Double where
  assume (+) :: Double -> Double -> Double
  assume (-) :: Double -> Double -> Double
  assume (*) :: Double -> Double -> Double
  assume negate :: Double -> Double
  assume abs :: Double -> Double
  assume signum :: Double -> Double
  assume fromInteger :: Integer -> Double

instance Fractional Float where
  assume (/) :: Float -> Float -> Float
  assume recip :: Float -> Float
  assume fromRational :: {r:Ratio Integer | NativeIEEEFromRationalDomain r} -> Float

instance Fractional Double where
  assume (/) :: Double -> Double -> Double
  assume recip :: Double -> Double
  assume fromRational :: {r:Ratio Integer | NativeIEEEFromRationalDomain r} -> Double

// rationalToFloat/rationalToDouble handle denominator zero themselves and
// return zero for numerator zero. Otherwise they normalize the numerator's
// sign before fromRat'', whose premise is n > 0 and d > 0. This is a
// sufficient raw-input domain, not an invariant on every Ratio constructor
// or a claim that every excluded negative-denominator input is partial.
predicate NativeIEEEFromRationalDomain R = denominator R >= 0 || numerator R = 0
@-}
