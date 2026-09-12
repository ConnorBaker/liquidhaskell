{-# OPTIONS_GHC -O2 #-}

{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module ImportedMeasureArrowLib (Arrow, wrap, run) where

newtype Arrow a b = Arrow (a -> b)

{-@ reflect wrap @-}
wrap :: (a -> b) -> Arrow a b
wrap function = Arrow function

{-@ reflect run @-}
run :: Arrow a b -> a -> b
run (Arrow function) value = function value

{-@ fail producerVacuity @-}
{-@ producerVacuity :: x:Int -> {v:Int | v > x} @-}
producerVacuity :: Int -> Int
producerVacuity x = x
