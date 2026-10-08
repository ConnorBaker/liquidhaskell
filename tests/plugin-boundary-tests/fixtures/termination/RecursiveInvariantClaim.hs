module RecursiveInvariantClaim where

data Empty = Step Empty

{-@ invariant {value:Empty | false} @-}

{-@ loop :: Empty / [0] @-}
loop :: Empty
loop = loop
