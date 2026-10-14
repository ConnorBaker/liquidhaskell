module OwnedInstancePreludeClient where

import OwnedInstanceGood (Pick (..))

{-@ same :: x:Int -> {v:Int | v == x} @-}
same :: Int -> Int
same x = pick x
