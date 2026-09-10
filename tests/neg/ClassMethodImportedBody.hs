{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module ClassMethodImportedBody where

import ClassMethodImportedSpec

data Unit = Unit

instance C Unit where
    one x = x
    many n x = if n > 0 then error "inside the admitted domain" else x

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x - 1
