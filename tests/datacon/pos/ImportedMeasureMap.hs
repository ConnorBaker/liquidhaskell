{-# OPTIONS_GHC -O2 #-}

{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--ple" @-}
module ImportedMeasureMap (fromMap) where

import qualified Data.Map.Strict as Map
import ImportedMeasureMapLib (largest)

{-@ fromMap :: values:Map.Map Int Int -> {v:Maybe (Int, Int) | v == largest values} @-}
fromMap :: Map.Map Int Int -> Maybe (Int, Int)
fromMap = largest

{-@ fail consumerVacuity @-}
{-@ consumerVacuity :: x:Int -> {v:Int | v > x} @-}
consumerVacuity :: Int -> Int
consumerVacuity x = x
