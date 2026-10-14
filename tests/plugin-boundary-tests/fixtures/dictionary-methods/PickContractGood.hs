-- A local instance contract, not the class name, decides the dictionary.
module PickContractGood (Pick (..), g) where

class Pick a where
  pickOne :: a -> a -> a

instance Pick Int where
  pickOne x _ = x

{-@ instance Pick Int where
      pickOne :: x:Int -> y:Int -> {v:Int | v = x} @-}

{-@ f :: Pick a => a -> a -> a @-}
f :: Pick a => a -> a -> a
f x y = pickOne x y

{-@ g :: {t:Int | t > 0} -> {t:Int | t > 0} -> {t:Int | t > 0} @-}
g :: Int -> Int -> Int
g x y = f x y
