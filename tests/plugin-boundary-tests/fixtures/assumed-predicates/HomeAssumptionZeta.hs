module HomeAssumptionZeta (g) where

import HomeAssumptionAlpha (f)

-- A non-home assumption about the imported f. Its module name sorts after
-- the home module's, so only home precedence can select the home contract.
{-@ assume f :: x:Int -> {v:Int | v == x + 1} @-}

g :: Int -> Int
g = f
