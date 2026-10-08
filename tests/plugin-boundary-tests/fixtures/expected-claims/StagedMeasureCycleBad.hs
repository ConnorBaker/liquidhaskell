module StagedMeasureCycleBad where

{-@ measure leftMeasure @-}
{-@ leftMeasure :: input:Bool -> {value:Integer | value == rightMeasure input} @-}
leftMeasure :: Bool -> Integer
leftMeasure False = 0
leftMeasure True = 0

{-@ measure rightMeasure @-}
{-@ rightMeasure :: input:Bool -> {value:Integer | value == leftMeasure input + 1} @-}
rightMeasure :: Bool -> Integer
rightMeasure False = 0
rightMeasure True = 0
