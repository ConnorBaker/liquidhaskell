module IntegerOrderingGood where

{-@ depthLess :: x:Integer -> y:Integer -> {v:Bool | v <=> x < y} @-}
depthLess :: Integer -> Integer -> Bool
depthLess = (<)

{-@ depthSame :: x:Integer -> y:Integer -> {v:Bool | v <=> x = y} @-}
depthSame :: Integer -> Integer -> Bool
depthSame = (==)

{-@ depthLessEq :: x:Integer -> y:Integer -> {v:Bool | v <=> x <= y} @-}
depthLessEq :: Integer -> Integer -> Bool
depthLessEq = (<=)

{-@ depthGreater :: x:Integer -> y:Integer -> {v:Bool | v <=> x > y} @-}
depthGreater :: Integer -> Integer -> Bool
depthGreater = (>)
