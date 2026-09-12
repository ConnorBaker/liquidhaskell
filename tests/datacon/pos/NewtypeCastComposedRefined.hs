{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}

-- Composition preserves both exact contents and the intermediate representation domain.
module NewtypeCastComposedRefined (Inner (..), Outer (..), values, wrap, extract) where

import Data.Coerce (coerce)

{-@ newtype Inner a = Inner { items :: {v:[a] | 0 < len v} } @-}
newtype Inner a = Inner { items :: [a] }
newtype Outer a = Outer (Inner a)

{-@ measure values @-}
values :: Outer a -> [a]
values (Outer inner) = items inner

{-@ wrap :: entries:{v:[a] | 0 < len v} -> {v:Outer a | values v == entries} @-}
wrap :: [a] -> Outer a
wrap = coerce

{-@ extract :: value:Outer a -> {v:[a] | 0 < len v && v == values value} @-}
extract :: Outer a -> [a]
extract = coerce

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
