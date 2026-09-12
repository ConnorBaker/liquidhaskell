{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}

-- Two type arguments and an eta-reduced map representation need no map axiom
-- to establish the constructor/field equation.
module NewtypeCastMap where

import Data.Map.Strict (Map)

newtype WrappedMap key value = WrappedMap (Map key value)

{-@ measure entries @-}
entries :: WrappedMap key value -> Map key value
entries (WrappedMap values) = values

{-@ wrap :: values:Map key value -> {v:WrappedMap key value | entries v == values} @-}
wrap :: Map key value -> WrappedMap key value
wrap values = WrappedMap values

{-@ extract :: value:WrappedMap key value -> {v:Map key value | v == entries value} @-}
extract :: WrappedMap key value -> Map key value
extract (WrappedMap values) = values

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | 0 < v} @-}
nonVacuity :: Int -> Int
nonVacuity argument = argument - 1
