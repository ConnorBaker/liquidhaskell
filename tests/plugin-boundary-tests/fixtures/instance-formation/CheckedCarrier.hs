module CheckedCarrier (Pick (..)) where

class Pick a where
    pick :: a -> a

{-@ instance Pick ({v:Int | v > 0}) where
      pick :: x:{v:Int | v > 0} -> {v:Int | v == x} @-}
instance Pick Int where
    pick x = x
