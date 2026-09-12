{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

module NewtypeFunctionCastDomainBad (Nonempty (..), extract, widened) where

import Data.Coerce (coerce)

{-@ newtype Nonempty a = Nonempty { items :: {v:[a] | 0 < len v} } @-}
newtype Nonempty a = Nonempty { items :: [a] }

{-# NOINLINE extract #-}
extract :: Nonempty a -> [a]
extract (Nonempty entries) = entries

widened :: [Int] -> [Int]
widened = coerce extract

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
