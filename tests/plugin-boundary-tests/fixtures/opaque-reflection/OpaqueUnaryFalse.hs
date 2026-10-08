module OpaqueUnaryFalse where

{-@ opaque-reflect p @-}
{-@ p :: Integer -> {v:Integer | False} @-}
p :: Integer -> Integer
p _ = 0
