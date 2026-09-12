{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

module NewtypeFunctionCastResultBad (Nonempty (..), emptyResult, invalid) where

import Data.Coerce (coerce)

{-@ newtype Nonempty a = Nonempty { items :: {v:[a] | 0 < len v} } @-}
newtype Nonempty a = Nonempty { items :: [a] }

{-# NOINLINE emptyResult #-}
{-@ emptyResult :: () -> {v:[Int] | len v == 0} @-}
emptyResult :: () -> [Int]
emptyResult () = []

invalid :: () -> Nonempty Int
invalid = coerce emptyResult

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
