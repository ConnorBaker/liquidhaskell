module InferredFunctionGood (g) where

{-# NOINLINE f #-}
f :: Integer -> Integer
f x = x + 1

{-@ g :: x:Integer -> {v:Integer | v == x + 1} @-}
g :: Integer -> Integer
g x = f x
