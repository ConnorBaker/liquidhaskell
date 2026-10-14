-- The superclass field of a known instance is itself a known instance and is
-- checked by its own method contracts: Ord Int's max returns an argument.
module SuperclassContractGood (Choose (..), g) where

class Ord a => Choose a where
  choose :: a -> a -> a

instance Choose Int where
  choose x _ = x

{-@ instance Choose Int where
      choose :: x:Int -> y:Int -> {v:Int | v = x} @-}

{-@ f :: Choose a => a -> a -> a @-}
f :: Choose a => a -> a -> a
f x y = max y (choose x y)

{-@ g :: {t:Int | t > 0} -> {t:Int | t > 0} -> {t:Int | t > 0} @-}
g :: Int -> Int -> Int
g x y = f x y
