module StructuralMixedFailure where

{-@ first :: xs:[Integer] -> {v:Integer | v == len xs} @-}
first :: [Integer] -> Integer
first [] = 0
first (_ : rest) = 1 + second rest

{-@ second :: xs:[Integer] -> {v:Integer | v == len xs} @-}
second :: [Integer] -> Integer
second [] = 1
second (_ : rest) = 1 + first rest
