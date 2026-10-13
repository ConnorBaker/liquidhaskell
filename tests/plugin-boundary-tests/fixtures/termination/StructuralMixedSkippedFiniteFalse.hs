module StructuralMixedSkippedFiniteFalse where

{-@ lazy second @-}
{-@ first :: xs:[Integer] -> {v:Integer | false} @-}
first :: [Integer] -> Integer
first [] = 0
first (_ : rest) = second rest

{-@ second :: xs:[Integer] -> {v:Integer | false} @-}
second :: [Integer] -> Integer
second [] = 0
second (_ : rest) = first rest
