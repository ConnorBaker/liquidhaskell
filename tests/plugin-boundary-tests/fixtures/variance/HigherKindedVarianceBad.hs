module HigherKindedVarianceBad where

data Negative a = Negative (a -> Int)

{-@ data Negative a = Negative { callback :: a -> Nat } @-}

data Applied f a = Applied (f a)

{-@ naturalId :: Nat -> Nat @-}
naturalId :: Int -> Int
naturalId x = x

{-@ seed :: Applied Negative Nat @-}
seed :: Applied Negative Int
seed = Applied (Negative naturalId)

{-@ widen :: Applied Negative Nat -> Applied Negative Int @-}
widen :: Applied Negative Int -> Applied Negative Int
widen x = x

{-@ forged :: Nat @-}
forged :: Int
forged = case widen seed of
    Applied (Negative f) -> f (-1)
