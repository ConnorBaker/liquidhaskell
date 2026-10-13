module StructuralFunctionTopFalse where

{-@ count :: {function:([Integer] -> Integer) | false} @-}
count :: [Integer] -> Integer
count [] = 0
count (_ : rest) = 1 + count rest
