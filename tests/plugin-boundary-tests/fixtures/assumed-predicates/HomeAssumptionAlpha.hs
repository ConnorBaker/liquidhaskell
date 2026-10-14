module HomeAssumptionAlpha (f) where

-- The defining module's own assumption is the home specification of f.
{-@ assume f :: x:Int -> {v:Int | v == x} @-}
f :: Int -> Int
f x = x
