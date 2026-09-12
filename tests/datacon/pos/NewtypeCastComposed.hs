{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}

module NewtypeCastComposed (Inner (..), Outer (..), innerValues, values, wrap, extract) where

import Data.Coerce (coerce)

newtype Inner a = Inner [a]
newtype Outer a = Outer (Inner a)

{-@ measure innerValues @-}
innerValues :: Inner a -> [a]
innerValues (Inner entries) = entries

{-@ measure values @-}
values :: Outer a -> [a]
values (Outer inner) = innerValues inner

{-@ wrap :: entries:[a] -> {v:Outer a | values v == entries} @-}
wrap :: [a] -> Outer a
wrap = coerce

{-@ extract :: value:Outer a -> {v:[a] | v == values value} @-}
extract :: Outer a -> [a]
extract = coerce

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
