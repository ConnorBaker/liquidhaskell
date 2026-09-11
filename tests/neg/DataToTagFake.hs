{-# LANGUAGE MagicHash, TypeApplications, ScopedTypeVariables, FlexibleContexts #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--total-Haskell" @-}
module DataToTagFake where
import GHC.Exts (Int(I#), Int#, dataToTag#, withDict)
import GHC.Magic (DataToTag)
data Choice = First Int | Second Int
{-# NOINLINE callGiven #-}
callGiven :: DataToTag a => a -> Int
callGiven value = I# (dataToTag# value)
fakeApply :: forall a. (a -> Int#) -> a -> Int
fakeApply method value = withDict @(DataToTag a) method (callGiven value)
fakeTag :: Choice -> Int#
fakeTag _ = 7#
-- This really returns 7, despite First's ordinary constructor tag being 0.
{-@ wrongDictionaryTag :: Int -> {v:Int | v == 0} @-}
wrongDictionaryTag :: Int -> Int
wrongDictionaryTag x = fakeApply fakeTag (First x)
{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | v > 0} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe x = x - 1
