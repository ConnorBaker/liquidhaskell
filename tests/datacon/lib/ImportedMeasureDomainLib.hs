{-# OPTIONS_GHC -O2 #-}

{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module ImportedMeasureDomainLib (NaturalAction (..), applyNatural) where

{-@ data NaturalAction = NaturalAction { runNatural :: Nat -> Nat } @-}
newtype NaturalAction = NaturalAction {runNatural :: Int -> Int}

{-@ reflect applyNatural @-}
{-@ applyNatural :: NaturalAction -> Nat -> Nat @-}
applyNatural :: NaturalAction -> Int -> Int
applyNatural (NaturalAction function) value = function value

{-@ fail producerVacuity @-}
{-@ producerVacuity :: x:Int -> {v:Int | v > x} @-}
producerVacuity :: Int -> Int
producerVacuity x = x
