{-# OPTIONS_GHC -O2 #-}

{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--ple" @-}
module ImportedMeasureMapWrong (wrong) where

import qualified Data.Map.Strict as Map
import ImportedMeasureMapLib (largest)

{-@ wrong :: values:Map.Map Int Int -> {v:Maybe (Int, Int) | v == largest values} @-}
wrong :: Map.Map Int Int -> Maybe (Int, Int)
wrong _ = Nothing

{-@ fail consumerVacuity @-}
{-@ consumerVacuity :: x:Int -> {v:Int | v > x} @-}
consumerVacuity :: Int -> Int
consumerVacuity x = x
