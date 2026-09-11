{-# LANGUAGE MagicHash #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--total-Haskell" @-}
module DataToTagWrong where
import GHC.Exts (Int(I#), dataToTag#)
data Choice = First Int | Second Int
{-@ wrongTag :: Int -> {v:Int | v == 1} @-}
wrongTag :: Int -> Int
wrongTag x = I# (dataToTag# (First x))
{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | v > 0} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe x = x - 1
