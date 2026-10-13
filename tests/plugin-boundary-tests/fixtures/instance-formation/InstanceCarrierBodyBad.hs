module InstanceCarrierBodyBad where

class Pick a where
    pick :: a -> a
    other :: a -> a

{-@ class Pick a where
      pick :: a -> a
      other :: a -> a @-}

{-@ instance Pick ({v:Int | v > 0}) where
      pick :: {v:Int | v > 1} -> {v:Int | v > 0}
      other :: {v:Int | v > 0} -> {v:Int | v > 0} @-}
instance Pick Int where
    pick x = x
    other x = x
