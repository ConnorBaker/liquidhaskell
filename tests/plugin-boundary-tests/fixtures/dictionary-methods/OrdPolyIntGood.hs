module OrdPolyIntGood (combine) where

{-@ pick :: Ord a => a -> a -> a @-}
pick :: Ord a => a -> a -> a
pick x y = if x <= y then x else y

{-@ combine :: {t:Int | t > 0} -> {t:Int | t > 0} -> {t:Int | t > 0} @-}
combine :: Int -> Int -> Int
combine x y = pick x y
