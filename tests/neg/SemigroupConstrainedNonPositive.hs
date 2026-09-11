{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module SemigroupConstrainedNonPositive where

import Data.Semigroup (stimes)

data Wrap a = Wrap a

instance (Semigroup a) => Semigroup (Wrap a) where
    Wrap x <> Wrap y = Wrap (x <> y)

invalidCall :: (Semigroup a) => a -> Wrap a
invalidCall x = stimes (0 :: Int) (Wrap x)

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x
