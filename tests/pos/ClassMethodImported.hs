{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module ClassMethodImported where

import ClassMethodLibrary

data Unit = Unit

instance C Unit where
    one x = x
    many n x = if n <= 0 then error "outside the imported method domain" else x

validCall :: Unit
validCall = many (1 :: Int) Unit

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x - 1
