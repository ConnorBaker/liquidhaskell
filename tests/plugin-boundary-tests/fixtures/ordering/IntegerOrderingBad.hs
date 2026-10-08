module IntegerOrderingBad where

{-@ depthLess :: x:Integer -> y:Integer -> {v:Bool | v <=> x < y} @-}
depthLess :: Integer -> Integer -> Bool
depthLess = (>)
