module ClassMethodWrongCarrier where

class Scalar a where
    scalar :: Int -> a -> a

{-@ class Scalar a where
      scalar :: Integer -> a -> a @-}
