module EnumFromToFalse (below) where

{-@ below :: lo:Int -> hi:Int -> [{v:Int | v < hi}] @-}
below :: Int -> Int -> [Int]
below lo hi = enumFromTo lo hi
