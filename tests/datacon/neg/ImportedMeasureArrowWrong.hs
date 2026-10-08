{-# OPTIONS_GHC -O2 #-}

{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--ple" @-}
module ImportedMeasureArrowWrong (wrong) where

import ImportedMeasureReexport (run, wrap)

{-@ wrong :: x:Bool -> {v:Bool | v == x} @-}
wrong :: Bool -> Bool
wrong value = run (wrap not) value

{-@ fail consumerVacuity @-}
{-@ consumerVacuity :: x:Int -> {v:Int | v > x} @-}
consumerVacuity :: Int -> Int
consumerVacuity x = x
