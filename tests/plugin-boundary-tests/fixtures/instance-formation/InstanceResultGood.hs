module InstanceResultGood where

class Pick a where
    pick :: a -> a
    other :: a -> a

{-@ class Pick a where
      pick :: a -> a
      other :: a -> a @-}

{-@ instance Pick Int where
      pick :: x:Int -> {v:Int | v == x}
      other :: Int -> Int @-}
instance Pick Int where
    pick x = x
    other x = x

good :: Int
good = pick 0
