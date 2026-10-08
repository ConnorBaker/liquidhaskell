module InferredConstantGood (use) where

{-# NOINLINE big #-}
big :: Int
big = 65536

{-@ requiresNonNeg :: {x:Int | 0 <= x} -> Int @-}
{-# NOINLINE requiresNonNeg #-}
requiresNonNeg :: Int -> Int
requiresNonNeg x = x

{-@ use :: Int @-}
use :: Int
use = requiresNonNeg big
