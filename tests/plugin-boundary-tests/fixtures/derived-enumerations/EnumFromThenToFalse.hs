module EnumFromThenToFalse (upward) where

{-@ upward :: x1:Int -> x2:Int -> y:Int -> [{v:Int | x1 <= v}] @-}
upward :: Int -> Int -> Int -> [Int]
upward x1 x2 y = enumFromThenTo x1 x2 y
