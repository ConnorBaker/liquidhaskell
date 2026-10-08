{-# OPTIONS_GHC -O2 #-}

{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--ple" @-}
module ImportedMeasureArrow (integerIdentity, booleanIdentity) where

import ImportedMeasureReexport (run, wrap)

{-@ integerIdentity :: x:Int -> {v:Int | v == x} @-}
integerIdentity :: Int -> Int
integerIdentity value = run (wrap id) value

{-@ booleanIdentity :: x:Bool -> {v:Bool | v == x} @-}
booleanIdentity :: Bool -> Bool
booleanIdentity value = run (wrap id) value

{-@ fail consumerVacuity @-}
{-@ consumerVacuity :: x:Int -> {v:Int | v > x} @-}
consumerVacuity :: Int -> Int
consumerVacuity x = x
