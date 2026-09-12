{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}

module NewtypeCastEmbedded (WrappedSet (..), wrap, unwrap, roundTrip) where

import Data.Coerce (coerce)
import Data.Set (Set)

{-@ embed WrappedSet as (Set_Set Int) @-}
newtype WrappedSet = WrappedSet (Set Int)

{-@ wrap :: values:Set Int -> {v:WrappedSet | v == values} @-}
wrap :: Set Int -> WrappedSet
wrap = WrappedSet

{-@ unwrap :: wrapped:WrappedSet -> {v:Set Int | v == wrapped} @-}
unwrap :: WrappedSet -> Set Int
unwrap = coerce

{-@ roundTrip :: values:Set Int -> {v:Set Int | v == values} @-}
roundTrip :: Set Int -> Set Int
roundTrip values = unwrap (wrap values)

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
