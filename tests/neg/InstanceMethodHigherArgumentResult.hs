{-# LANGUAGE RankNTypes #-}

{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module InstanceMethodHigherArgumentResult where

class Higher a where
    higher :: (forall b. (Integral b) => b -> b) -> a -> Int -> Int

{-@ class Higher a where
      higher :: (forall b. Integral b => {n:b | n > 0} -> {v:b | v > 0})
             -> a -> {n:Int | n > 0} -> {v:Int | v > 0}
  @-}

data Token a = Token a

instance (Eq a) => Higher (Token a) where
    higher _ _ _ = 0

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x
