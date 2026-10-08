module InterleavedMethodEvidence where

class Extra a where
    extra :: a -> Int
    extraTag :: a -> Bool

{-@ instance Extra Int where
      extra :: x:Int -> {v:Int | v == x};
      extraTag :: Int -> Bool @-}
instance Extra Int where
    extra x = x
    extraTag _ = True

class Source a where
    selected :: (Extra b) => a -> b -> Int
    sourceTag :: a -> Bool

{-@ instance Source Int where
      selected :: forall b. Extra b => x:Int -> b -> {v:Int | v == x};
      sourceTag :: Int -> Bool @-}
instance Source Int where
    selected x _ = x
    sourceTag _ = True
    {-# NOINLINE selected #-}

{-@ client :: x:Int -> y:{Int | y /= x} -> {v:Int | v == y} @-}
client :: Int -> Int -> Int
client x y = selected x y
{-# NOINLINE client #-}
