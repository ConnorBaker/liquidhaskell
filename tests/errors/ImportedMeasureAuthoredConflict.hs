{-# OPTIONS_GHC -O2 #-}

{-@ LIQUID "--expect-error-containing=Multiple specifications for `value`" @-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
module ImportedMeasureAuthoredConflict (Box (..)) where

{-@ data Box = Box { value :: Nat } @-}
data Box = Box Int

{-@ measure value :: Box -> Int
      value (Box field) = 0
  @-}

{-@ fail consumerVacuity @-}
{-@ consumerVacuity :: x:Int -> {v:Int | v > x} @-}
consumerVacuity :: Int -> Int
consumerVacuity x = x
