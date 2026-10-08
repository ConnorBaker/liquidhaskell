module ForeignAssumptionGood where

import Data.Char (ord)

{-@ opaque-reflect positive @-}
{-@ positive :: {x:Integer | 0 < x} -> Integer @-}
positive :: Integer -> Integer
positive x = x

{-@ assume ord :: Char -> {v:Int | 0 <= positive 1} @-}
