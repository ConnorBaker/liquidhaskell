-- A user class whose instance fabricates its result, without a contract.
module PickFabLib (Pick (..), f) where

class Pick a where
  pickOne :: a -> a -> a
  pickName :: a -> Int

instance Pick Int where
  pickOne _ _ = 0
  pickName _ = 1

{-@ f :: Pick a => a -> a -> a @-}
f :: Pick a => a -> a -> a
f x y = pickOne x y
{-# NOINLINE f #-}
