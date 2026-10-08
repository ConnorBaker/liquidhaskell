module RecursiveValueClaim where

{-@ loop :: {v:Integer | false} / [0] @-}
loop :: Integer
loop = loop
