{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}

-- GHC eta-reduces the consumer to a polymorphic function cast of entries.
-- Its argument conversion must retain the wrapped map's exact interpretation.
module NewtypeFunctionCastMap (WrappedMap (..), entries, roundtrip) where

import Data.Map.Strict (Map)

newtype WrappedMap key value = WrappedMap (Map key value)

{-@ measure entries @-}
{-@ entries :: wrapped:WrappedMap key value -> {v:Map key value | v == entries wrapped} @-}
entries :: WrappedMap key value -> Map key value
entries (WrappedMap values) = values

{-@ roundtrip :: values:Map key value -> {v:Map key value | v == values} @-}
roundtrip :: Map key value -> Map key value
roundtrip values = entries (WrappedMap values)

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
