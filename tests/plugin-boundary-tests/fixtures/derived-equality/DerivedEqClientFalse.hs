module DerivedEqClientFalse where

import DerivedEqProducer

{-@ alwaysEqual :: Color -> Color -> {v:Bool | v} @-}
alwaysEqual :: Color -> Color -> Bool
alwaysEqual x y = x == y
