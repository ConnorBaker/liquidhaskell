module HomeAssumptionClientGood where

import HomeAssumptionAlpha (f)
import HomeAssumptionZeta (g)

{-@ h :: x:Int -> {v:Int | v == x} @-}
h :: Int -> Int
h x = f x
