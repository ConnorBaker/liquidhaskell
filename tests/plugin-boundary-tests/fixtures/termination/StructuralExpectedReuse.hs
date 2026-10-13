module StructuralExpectedReuse where

{-@ fail count @-}
{-@ count :: xs:[Integer] -> {v:Integer | v == len xs} @-}
count :: [Integer] -> Integer
count [] = 1
count (_ : rest) = 1 + count rest

{-@ client :: xs:[Integer] -> {v:Integer | v == len xs} @-}
client :: [Integer] -> Integer
client = count
