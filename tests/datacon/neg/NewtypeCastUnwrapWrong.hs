{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- Unwrapping preserves this argument's contents, not an unrelated argument's.
module NewtypeCastUnwrapWrong (Box (..), contents, wrong) where

newtype Box a = Box [a]

{-@ measure contents @-}
contents :: Box a -> [a]
contents (Box entries) = entries

{-@ wrong :: first:Box Int -> second:Box Int -> {v:[Int] | v == contents second} @-}
wrong :: Box Int -> Box Int -> [Int]
wrong (Box entries) _ = entries

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
