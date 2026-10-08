module InferredHoleFalse (g) where

{-@ f :: _ -> _ @-}
{-# NOINLINE f #-}
f :: Integer -> Integer
f x = x + 1

{-@ g :: x:Integer -> {v:Integer | v == x + 2} @-}
g :: Integer -> Integer
g x = f x
