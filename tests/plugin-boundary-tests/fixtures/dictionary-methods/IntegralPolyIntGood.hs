-- Integral's class fields state div's divisor domain through its superclass
-- field, so the dictionary keeps the ordinary judgment; Int remains valid.
module IntegralPolyIntGood (g) where

{-@ half :: Integral a => a -> a @-}
half :: Integral a => a -> a
half x = x `div` 2
{-# NOINLINE half #-}

{-@ g :: Int -> Int @-}
g :: Int -> Int
g x = half x
