module InstanceCarrierDuplicateBad where

class Pick a where
    pick :: a -> a

{-@ instance Pick ({v:Int | v > 0}) where
      pick :: {v:Int | v > 0} -> {v:Int | v > 0} @-}
{-@ instance Pick ({v:Int | v > 1}) where
      pick :: {v:Int | v > 1} -> {v:Int | v > 1} @-}
instance Pick Int where
    pick x = x
