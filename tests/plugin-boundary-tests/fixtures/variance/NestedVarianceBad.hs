module NestedVarianceBad where

data D a = Stop a | Next (D (a -> Int))

{-@ data D a = Stop { stopValue :: a }
             | Next { nextValue :: D (a -> Nat) } @-}

{-@ naturalId :: Nat -> Nat @-}
naturalId :: Int -> Int
naturalId x = x

{-@ seed :: D Nat @-}
seed :: D Int
seed = Next (Stop naturalId)

{-@ widen :: D Nat -> D Int @-}
widen :: D Int -> D Int
widen x = x

{-@ forged :: Nat @-}
forged :: Int
forged = case widen seed of
    Next (Stop f) -> f (-1)
    _ -> 0
