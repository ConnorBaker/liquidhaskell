{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module SemigroupTotalOverride where

import Data.Semigroup (stimes)

data Unit = Unit

instance Semigroup Unit where
    Unit <> Unit = Unit
    stimes _ x = x

-- A particular implementation can admit more than the common class domain.
{-@ instance Semigroup Unit where
      stimes :: forall b. Integral b => b -> Unit -> Unit
  @-}

zero :: Unit
zero = stimes (0 :: Int) Unit

negative :: Unit
negative = stimes (-1 :: Int) Unit

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x - 1
