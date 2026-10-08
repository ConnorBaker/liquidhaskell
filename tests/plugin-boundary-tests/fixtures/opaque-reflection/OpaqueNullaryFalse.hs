module OpaqueNullaryFalse where

{-@ opaque-reflect p @-}
{-@ p :: {v:Integer | False} @-}
p :: Integer
p = 0
