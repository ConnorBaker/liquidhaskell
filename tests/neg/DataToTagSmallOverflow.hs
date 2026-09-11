{-# LANGUAGE MagicHash #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--total-Haskell" @-}
module DataToTagSmallOverflow where
import GHC.Exts (Int(I#))
import GHC.Prim (dataToTagSmall#)
data Nine = N0 Int | N1 Int | N2 Int | N3 Int | N4 Int
          | N5 Int | N6 Int | N7 Int | N8 Int
-- The Small primitive is not defined for all constructors of this datatype.
{-@ wrongSmallTag :: Nine -> {v:Int | 0 <= v && v < 9} @-}
wrongSmallTag :: Nine -> Int
wrongSmallTag x = I# (dataToTagSmall# x)
{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | v > 0} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe x = x - 1
