-- The method contract holds, but the superclass instance has no contracts and
-- its max fabricates K 0.
module SuperclassFabFalse (K (..), Choose (..), g) where

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

class Ord a => Choose a where
  choose :: a -> a -> a

instance Choose K where
  choose x _ = x

{-@ instance Choose K where
      choose :: x:K -> y:K -> {v:K | v = x} @-}

{-@ f :: Choose a => a -> a -> a @-}
f :: Choose a => a -> a -> a
f x y = max y (choose x y)

{-@ g :: {k:K | kv k > 0} -> {k:K | kv k > 0} -> {k:K | kv k > 0} @-}
g :: K -> K -> K
g x y = f x y
