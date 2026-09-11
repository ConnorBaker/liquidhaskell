{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module InstanceMethodTotal where

class Dispatch a where
    dispatch :: a -> Int -> Int

data Token a = Token a

-- Preserve the instance context and its polymorphic payload.
instance (Eq a) => Dispatch (Token a) where
    dispatch (Token x) n = if x == x then n else 0

class Higher a where
    higher :: (Integral b) => a -> b -> b

-- Preserve method-local quantification and constraints as well.
instance Higher (Token a) where
    higher _ n = n

genericCall :: (Dispatch a) => a -> Int
genericCall x = dispatch x 0

reachable :: Int
reachable = genericCall (Token True)

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x
