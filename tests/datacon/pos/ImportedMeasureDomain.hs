{-# OPTIONS_GHC -O2 #-}

{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--ple" @-}
module ImportedMeasureDomain (naturalResult) where

import ImportedMeasureDomainLib (NaturalAction (..), applyNatural)

-- The imported field accepts any callback satisfying its declared domain and
-- result contract. Exact callback identity is tested through the reflected
-- Arrow producer, independently of this constructor-contract control.
{-@ naturalResult :: (Nat -> Nat) -> Nat -> Nat @-}
naturalResult :: (Int -> Int) -> Int -> Int
naturalResult callback value = applyNatural (NaturalAction callback) value

{-@ fail consumerVacuity @-}
{-@ consumerVacuity :: x:Int -> {v:Int | v > x} @-}
consumerVacuity :: Int -> Int
consumerVacuity x = x
