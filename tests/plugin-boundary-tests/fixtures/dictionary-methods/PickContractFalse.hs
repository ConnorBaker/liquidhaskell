module PickContractFalse (Pick (..), g) where

class Pick a where
  pickOne :: a -> a -> a

instance Pick Int where
  pickOne _ _ = 0

{-@ instance Pick Int where
      pickOne :: x:Int -> y:Int -> {v:Int | v = 0} @-}

{-@ f :: Pick a => a -> a -> a @-}
f :: Pick a => a -> a -> a
f x y = pickOne x y

{-@ g :: {t:Int | t > 0} -> {t:Int | t > 0} -> {t:Int | t > 0} @-}
g :: Int -> Int -> Int
g x y = f x y
