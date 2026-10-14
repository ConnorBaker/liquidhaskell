-- A lawless instance without method contracts: max and min fabricate K 0.
module OrdFabLib (K (..), kv, h) where

data K = K Int

{-@ measure kv @-}
kv :: K -> Int
kv (K n) = n

instance Eq K where
  K a == K b = a == b

instance Ord K where
  compare (K a) (K b) = compare a b
  max _ _ = K 0
  min _ _ = K 0

{-@ h :: Ord a => a -> a -> a @-}
h :: Ord a => a -> a -> a
h x y = max x y
{-# NOINLINE h #-}
