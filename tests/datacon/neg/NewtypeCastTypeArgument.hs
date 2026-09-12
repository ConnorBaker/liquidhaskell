{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

module NewtypeCastTypeArgument (Nonempty (..), invalid) where

{-@ newtype Nonempty a = Nonempty { items :: {v:[a] | len v > 0} } @-}
newtype Nonempty a = Nonempty { items :: [a] }

{-@ invalid :: () -> Nonempty Nat @-}
invalid :: () -> Nonempty Int
invalid () = Nonempty [-1]

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
