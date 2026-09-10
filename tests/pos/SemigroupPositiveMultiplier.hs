{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module SemigroupPositiveMultiplier where

import Data.Semigroup (stimes)

data Unit = Unit

instance Semigroup Unit where
    Unit <> Unit = Unit

{-@ repeatPositive :: (Semigroup a, Integral b) => {n:b | n > 0} -> a -> a @-}
repeatPositive :: (Semigroup a, Integral b) => b -> a -> a
repeatPositive n x = stimes n x

validCall :: Unit
validCall = repeatPositive (2 :: Int) Unit

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x - 1
