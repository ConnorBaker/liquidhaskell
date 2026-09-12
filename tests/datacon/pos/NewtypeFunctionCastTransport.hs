{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}

module NewtypeFunctionCastTransport (Box (..), transport) where

import Data.Coerce (coerce)

newtype Box a = Box { items :: [a] }

{-@ measure items @-}

{-@ transport :: (entries:[Int] -> {v:[Int] | v == entries}) -> box:Box Int -> {v:Box Int | items v == items box} @-}
transport :: ([Int] -> [Int]) -> Box Int -> Box Int
transport function = coerce function

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
