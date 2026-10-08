{-@ LIQUID "--expect-error-containing=duplicate measure pattern binder" @-}
{-@ LIQUID "--total-Haskell" @-}
module MeasurePatternDuplicate where

data Pair = Pair Int Int

{-@ measure repeated :: Pair -> Int
      repeated (Pair value value) = value
  @-}

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | v > 0} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe x = x - 1
