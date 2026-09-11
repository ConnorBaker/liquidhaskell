{-# LANGUAGE RankNTypes #-}

{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module InstanceMethodHigherArgument where

class Higher a where
    higher :: (forall b. (Integral b) => b -> b) -> a -> Int -> Int

{-@ class Higher a where
      higher :: (forall b. Integral b => {n:b | n > 0} -> {v:b | v > 0})
             -> a -> {n:Int | n > 0} -> {v:Int | v > 0}
  @-}

data Token a = Token a

instance (Eq a) => Higher (Token a) where
    higher f _ n = f n

{-@ good :: {n:Int | n > 0} -> {v:Int | v > 0} @-}
good :: Int -> Int
good n = higher (\x -> x) (Token True) n

{-@ fail badHigherArgument @-}
{-@ badHigherArgument :: {n:Int | n > 0} -> {v:Int | v > 0} @-}
badHigherArgument :: Int -> Int
badHigherArgument n = higher (\_ -> 0) (Token True) n

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x
