module ExpectedMeasureGood (f) where

{-@ f :: x:Bool -> {v:Integer | v == privateMeasure x} @-}
f :: Bool -> Integer
f False = 0
f True = 0

{-@ fail privateMeasure @-}
{-@ measure privateMeasure @-}
{-@ privateMeasure :: Bool -> {v:Integer | False} @-}
privateMeasure :: Bool -> Integer
privateMeasure False = 0
privateMeasure True = 0
