module DerivedEqFalse where

data Color = Red | Green | Blue deriving (Eq)

data Pair = Pair Int Integer deriving (Eq)

{-@ alwaysEqual :: Color -> Color -> {v:Bool | v} @-}
alwaysEqual :: Color -> Color -> Bool
alwaysEqual x y = x == y

{-@ inverted :: x:Pair -> y:Pair -> {v:Bool | v <=> x != y} @-}
inverted :: Pair -> Pair -> Bool
inverted x y = x == y

{-@ vacuous :: x:Pair -> y:Pair -> {v:Bool | false} @-}
vacuous :: Pair -> Pair -> Bool
vacuous x y = x == y
