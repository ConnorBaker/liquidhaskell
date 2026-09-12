{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

module NewtypeFunctionCastBottomBad (Box (..), invalid) where

import Data.Coerce (coerce)

newtype Box a = Box [a]

invalid :: () -> Bool
invalid () = (coerce (undefined :: [Int] -> [Int]) :: Box Int -> Box Int) `seq` True

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
