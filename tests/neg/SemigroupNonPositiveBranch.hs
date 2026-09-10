{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
module SemigroupNonPositiveBranch where

import Data.Semigroup (stimes)

data Unit = Unit

instance Semigroup Unit where
    Unit <> Unit = Unit

invalidCall :: Int -> Unit
invalidCall n = if n <= 0 then stimes n Unit else Unit

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x - 1
