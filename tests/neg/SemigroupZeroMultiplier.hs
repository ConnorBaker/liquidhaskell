{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module SemigroupZeroMultiplier where

import Data.Semigroup (stimes)

-- Generic dispatch cannot rely on a particular total override.
invalidCall :: (Semigroup a) => a -> a
invalidCall x = stimes (0 :: Int) x

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x - 1
