{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}

module NewtypeFunctionCastResult (Nonempty (..), singleton, wrapSingleton) where

import Data.Coerce (coerce)

{-@ newtype Nonempty a = Nonempty { items :: {v:[a] | 0 < len v} } @-}
newtype Nonempty a = Nonempty { items :: [a] }

{-# NOINLINE singleton #-}
{-@ singleton :: entry:Int -> {v:[Int] | v == [entry] && len v == 1} @-}
singleton :: Int -> [Int]
singleton entry = [entry]

{-@ wrapSingleton :: entry:Int -> {v:Nonempty Int | items v == [entry]} @-}
wrapSingleton :: Int -> Nonempty Int
wrapSingleton = coerce singleton

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
