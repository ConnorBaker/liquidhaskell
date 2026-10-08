{-# OPTIONS_GHC -O2 #-}

{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

module PolymorphicEmptyFalseMember (Token (..), wrong) where

import qualified Data.Set as Set

data Token = First | Second
    deriving (Eq, Ord)

{-@ wrong :: token:Token -> {v:Bool | v} @-}
wrong :: Token -> Bool
wrong token = Set.member token Set.empty

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
