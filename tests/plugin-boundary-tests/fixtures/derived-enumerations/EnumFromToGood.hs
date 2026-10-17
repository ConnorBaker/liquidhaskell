module EnumFromToGood (within) where

{-@ within :: lo:Int -> hi:Int -> [{v:Int | lo <= v && v <= hi}] @-}
within :: Int -> Int -> [Int]
within lo hi = enumFromTo lo hi
