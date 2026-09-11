{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module SemigroupConstrainedInstance where

import Data.Semigroup (stimes)

data Wrap a = Wrap a

-- The generated method has an outer Semigroup dictionary followed by a
-- method-local forall b and Integral b dictionary. Neither can be erased.
instance (Semigroup a) => Semigroup (Wrap a) where
    Wrap x <> Wrap y = Wrap (x <> y)

positive :: (Semigroup a) => a -> Wrap a
positive x = stimes (2 :: Int) (Wrap x)

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x
