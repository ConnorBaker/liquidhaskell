module InstanceCarrierGood where

class Pick a where
    pick :: a -> a
    other :: a -> a

{-@ class Pick a where
      pick :: a -> a
      other :: a -> a @-}

{-@ instance Pick ({v:Int | v > 0}) where
      pick :: x:{v:Int | v > 0} -> {v:Int | v == x}
      other :: {v:Int | v > 0} -> {v:Int | v > 0} @-}
instance Pick Int where
    pick x = x
    other x = x

generic :: (Pick a) => a -> a
generic = pick
{-# NOINLINE generic #-}

good :: Int
good = generic 1
