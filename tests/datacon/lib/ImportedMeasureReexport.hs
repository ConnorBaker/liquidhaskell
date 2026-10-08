{-# OPTIONS_GHC -O2 #-}

{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
module ImportedMeasureReexport (module ImportedMeasureArrowLib, module ImportedMeasureMapLib) where

import ImportedMeasureArrowLib
import ImportedMeasureMapLib

{-@ fail reexportVacuity @-}
{-@ reexportVacuity :: x:Int -> {v:Int | v > x} @-}
reexportVacuity :: Int -> Int
reexportVacuity x = x
