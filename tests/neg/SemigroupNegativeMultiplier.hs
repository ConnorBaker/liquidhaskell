{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module SemigroupNegativeMultiplier where

import Data.Semigroup (stimes)

data Unit = Unit

instance Semigroup Unit where
    Unit <> Unit = Unit

invalidCall :: Unit
invalidCall = stimes (-1 :: Int) Unit

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x - 1
