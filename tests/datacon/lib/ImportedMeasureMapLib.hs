{-# OPTIONS_GHC -O2 #-}

{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module ImportedMeasureMapLib (largest) where

import qualified Data.Map.Strict as Map

{-@ reflect Map.lookupMax @-}
{-@ reflect largest @-}
largest :: Map.Map Int Int -> Maybe (Int, Int)
largest = Map.lookupMax

{-@ fail producerVacuity @-}
{-@ producerVacuity :: x:Int -> {v:Int | v > x} @-}
producerVacuity :: Int -> Int
producerVacuity x = x
