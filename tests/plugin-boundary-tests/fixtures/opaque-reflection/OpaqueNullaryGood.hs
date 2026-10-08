module OpaqueNullaryGood where

{-@ opaque-reflect p @-}
{-@ p :: {v:Integer | v == 0} @-}
p :: Integer
p = 0
