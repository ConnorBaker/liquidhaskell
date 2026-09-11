{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module InstanceMethodSpecializedPartial (reachable) where

data Broken a = Broken a

instance (Eq a) => Eq (Broken a) where
    {-# SPECIALIZE instance Eq (Broken Int) #-}
    _ == _ = error "partial specialized instance"

reachable :: Bool
reachable = Broken (0 :: Int) == Broken 0

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x
