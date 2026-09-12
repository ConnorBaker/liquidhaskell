{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

module NewtypeFunctionCastContentBad (Box (..), discard, wrong) where

import Data.Coerce (coerce)

newtype Box a = Box { items :: [a] }

{-# NOINLINE discard #-}
{-@ discard :: Box Int -> {v:[Int] | len v == 0} @-}
discard :: Box Int -> [Int]
discard _ = []

{-@ wrong :: entries:[Int] -> {v:[Int] | v == entries} @-}
wrong :: [Int] -> [Int]
wrong = coerce discard

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
