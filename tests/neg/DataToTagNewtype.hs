{-# LANGUAGE MagicHash #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--total-Haskell" @-}
module DataToTagNewtype where
import GHC.Exts (Int(I#))
import GHC.Prim (dataToTagSmall#)
data Choice = First Int | Second Int
newtype Wrapped = Wrapped Choice
-- A newtype has no independent runtime constructor numbered zero.
{-@ wrongNewtypeTag :: Wrapped -> {v:Int | v == 0} @-}
wrongNewtypeTag :: Wrapped -> Int
wrongNewtypeTag x = I# (dataToTagSmall# x)
{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | v > 0} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe x = x - 1
