module HomeAssumptionClientBad where

import HomeAssumptionAlpha (f)
import HomeAssumptionZeta (g)

{-@ h :: x:Int -> {v:Int | v == x + 1} @-}
h :: Int -> Int
h x = f x
