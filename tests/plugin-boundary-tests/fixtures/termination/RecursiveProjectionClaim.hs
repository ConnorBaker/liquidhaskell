module RecursiveProjectionClaim where

data Knot = Knot Knot

{-@ loop :: Knot / [0] @-}
loop :: Knot
loop =
    let
        {-# NOINLINE field #-}
        field = case loop of Knot child -> child
     in
        Knot field
