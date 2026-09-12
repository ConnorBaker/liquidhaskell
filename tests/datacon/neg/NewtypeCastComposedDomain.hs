{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- An unrestricted input cannot bypass an intermediate newtype's nonempty domain.
module NewtypeCastComposedDomain (Inner (..), Outer (..), invalid) where

import Data.Coerce (coerce)

{-@ newtype Inner a = Inner { items :: {v:[a] | 0 < len v} } @-}
newtype Inner a = Inner { items :: [a] }
newtype Outer a = Outer (Inner a)

invalid :: [Int] -> Outer Int
invalid = coerce

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
