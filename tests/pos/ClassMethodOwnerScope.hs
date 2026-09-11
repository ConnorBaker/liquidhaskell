{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--eliminate=all" @-}
module ClassMethodOwnerScope where

import qualified Data.Semigroup as Standard

-- This method has the same occurrence name as Semigroup.stimes but the
-- opposite domain. Matching by occurrence is valid only within its owner.
class Other a where
    stimes :: Int -> a -> a

{-@ class Other a where
      stimes :: {n:Int | n < 0} -> a -> a
  @-}

data Unit = Unit

instance Semigroup Unit where
    Unit <> Unit = Unit

instance Other Unit where
    stimes n x = if n >= 0 then error "outside Other's domain" else x

standardCall :: Unit
standardCall = Standard.stimes (1 :: Int) Unit

otherCall :: Unit
otherCall = stimes (-1) Unit

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x - 1
