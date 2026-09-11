{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--eliminate=all" @-}
module SemigroupZeroEliminateAll where

import Data.Semigroup (stimes)

data Unit = Unit

instance Semigroup Unit where
    Unit <> Unit = Unit

invalidCall :: Unit
invalidCall = stimes (0 :: Int) Unit

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x - 1
