module StructuralReflectedGood where

{-@ reflect count @-}
{-@ count :: xs:[Integer] -> {v:Integer | v == len xs} @-}
count :: [Integer] -> Integer
count [] = 0
count (_ : rest) = 1 + count rest
