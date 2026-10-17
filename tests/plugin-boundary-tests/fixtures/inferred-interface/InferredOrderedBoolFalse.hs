module InferredOrderedBoolFalse where

{-@ opaque-reflect noneLeft @-}
noneLeft :: [Int] -> Bool
noneLeft [] = False
noneLeft (_ : rest) = noneLeft rest

{-@ useNoneLeft :: [Int] -> {v:Bool | v} @-}
useNoneLeft :: [Int] -> Bool
useNoneLeft values = noneLeft values
