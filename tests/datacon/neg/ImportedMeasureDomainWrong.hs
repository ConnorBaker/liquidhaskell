{-# OPTIONS_GHC -O2 #-}

{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--ple" @-}
module ImportedMeasureDomainWrong (outsideDomain) where

import ImportedMeasureDomainLib (NaturalAction (..), applyNatural)

outsideDomain :: Int
outsideDomain = applyNatural (NaturalAction id) (-1)

{-@ fail consumerVacuity @-}
{-@ consumerVacuity :: x:Int -> {v:Int | v > x} @-}
consumerVacuity :: Int -> Int
consumerVacuity x = x
