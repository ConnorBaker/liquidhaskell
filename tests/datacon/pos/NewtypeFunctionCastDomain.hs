{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}

module NewtypeFunctionCastDomain (Nonempty (..), extract, roundtrip) where

import Data.Coerce (coerce)

{-@ newtype Nonempty a = Nonempty { items :: {v:[a] | 0 < len v} } @-}
newtype Nonempty a = Nonempty { items :: [a] }

{-# NOINLINE extract #-}
{-@ extract :: box:Nonempty a -> {v:[a] | v == items box && 0 < len v} @-}
extract :: Nonempty a -> [a]
extract (Nonempty entries) = entries

{-@ roundtrip :: entries:{v:[a] | 0 < len v} -> {v:[a] | v == entries} @-}
roundtrip :: [a] -> [a]
roundtrip = coerce extract

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
