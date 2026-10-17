module ApplicationCarrierFalse where

{-@ firstNatural :: (Int, f a)<{\x y -> 0 <= x}> -> {v:Int | 0 < v} @-}
firstNatural :: (Int, f a) -> Int
firstNatural (n, _) = n

{-@ firstAboveOne :: (Int, f a)<{\x y -> 0 < x}> -> {v:Int | 1 < v} @-}
firstAboveOne :: (Int, f a) -> Int
firstAboveOne (n, _) = n
