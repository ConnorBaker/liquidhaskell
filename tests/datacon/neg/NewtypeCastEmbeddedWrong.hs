{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

module NewtypeCastEmbeddedWrong (WrappedSet (..), forged) where

import Data.Set (Set)

{-@ embed WrappedSet as (Set_Set Int) @-}
newtype WrappedSet = WrappedSet (Set Int)

{-@ forged :: values:Set Int -> {v:WrappedSet | v /= values} @-}
forged :: Set Int -> WrappedSet
forged = WrappedSet

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
