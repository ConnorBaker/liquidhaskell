module StructuralLocalWrongBase where

{-@ outer :: xs:[Integer] -> {v:Integer | v == len xs} @-}
outer :: [Integer] -> Integer
outer xs = count xs
  where
    {-@ count :: ys:[Integer] -> {v:Integer | v == len ys} @-}
    count :: [Integer] -> Integer
    count [] = 1
    count (_ : rest) = 1 + count rest
