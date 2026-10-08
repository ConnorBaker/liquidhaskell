module DefaultHoleGood (use) where

{-@ onlyTrue :: {b:Bool | b} -> Integer @-}
{-# NOINLINE onlyTrue #-}
onlyTrue :: Bool -> Integer
onlyTrue True = 0

{-@ f :: _ -> _ @-}
{-# NOINLINE f #-}
f :: Bool -> Integer
f b = onlyTrue b

{-@ use :: {b:Bool | b} -> Integer @-}
use :: Bool -> Integer
use b = f b
