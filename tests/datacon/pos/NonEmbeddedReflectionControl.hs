{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module NonEmbeddedReflectionControl (Choice (..), flipChoice, involution, disjoint) where

data Choice = LeftChoice Int | RightChoice Int

{-@ reflect flipChoice @-}
flipChoice :: Choice -> Choice
flipChoice (LeftChoice value) = RightChoice value
flipChoice (RightChoice value) = LeftChoice value

{-@ involution :: choice:Choice -> {flipChoice (flipChoice choice) == choice} @-}
involution :: Choice -> ()
involution (LeftChoice _) = ()
involution (RightChoice _) = ()

{-@ disjoint :: value:Int -> {LeftChoice value /= RightChoice value} @-}
disjoint :: Int -> ()
disjoint _ = ()

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
