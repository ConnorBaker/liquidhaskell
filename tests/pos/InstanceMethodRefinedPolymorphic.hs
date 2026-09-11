{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module InstanceMethodRefinedPolymorphic where

class Dispatch a where
    dispatch :: a -> Int -> Int

{-@ class Dispatch a where
      dispatch :: a -> {n:Int | n > 0} -> Int
  @-}

data Token a = Token a

-- The class domain belongs to the dictionary's declared class, independent
-- of the type and evidence lambdas around the dictionary implementation.
instance (Eq a) => Dispatch (Token a) where
    {-# SPECIALIZE instance Dispatch (Token Int) #-}
    dispatch _ n = if n > 0 then n else error "unreachable at the class domain"

good :: Int
good = dispatch (Token True) 1

specializedGood :: Int
specializedGood = dispatch (Token (0 :: Int)) 1

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x
