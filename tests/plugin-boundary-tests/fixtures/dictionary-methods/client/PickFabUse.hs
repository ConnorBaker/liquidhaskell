module PickFabUse (g) where

import PickFabLib

{-@ g :: {t:Int | t > 0} -> {t:Int | t > 0} -> {t:Int | t > 0} @-}
g :: Int -> Int -> Int
g x y = f x y
