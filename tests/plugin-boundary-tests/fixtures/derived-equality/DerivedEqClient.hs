module DerivedEqClient where

import DerivedEqProducer

{-@ samePair :: x:Pair -> y:Pair -> {v:Bool | v <=> x == y} @-}
samePair :: Pair -> Pair -> Bool
samePair x y = x == y
