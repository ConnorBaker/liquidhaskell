module InferredDomainFalse (use) where

{-@ positiveOnly :: {x:Integer | 0 < x} -> Integer @-}
{-# NOINLINE positiveOnly #-}
positiveOnly :: Integer -> Integer
positiveOnly x = x

{-# NOINLINE f #-}
f :: Integer -> Integer
f x = positiveOnly x

{-@ use :: Integer -> Integer @-}
use :: Integer -> Integer
use x = f x
