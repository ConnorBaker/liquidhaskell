module EnumFromThenToGood (between) where

{-@ between :: x1:Int -> x2:Int -> y:Int -> [{v:Int | (x1 <= v && v <= y) || (y <= v && v <= x1)}] @-}
between :: Int -> Int -> Int -> [Int]
between x1 x2 y = enumFromThenTo x1 x2 y
