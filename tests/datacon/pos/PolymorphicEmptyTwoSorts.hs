{-# OPTIONS_GHC -O2 #-}

{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module PolymorphicEmptyTwoSorts (Token (..), emptyTokens, emptyInts, preserveTokens) where

import qualified Data.Set as Set

data Token = First | Second
    deriving (Eq, Ord)

{-@ emptyTokens :: () -> {v:Set.Set Token | Set_emp v} @-}
emptyTokens :: () -> Set.Set Token
emptyTokens () = Set.empty

{-@ emptyInts :: () -> {v:Set.Set Int | Set_emp v} @-}
emptyInts :: () -> Set.Set Int
emptyInts () = Set.empty

{-@ preserveTokens :: values:Set.Set Token -> {v:Set.Set Token | v == values} @-}
preserveTokens :: Set.Set Token -> Set.Set Token
preserveTokens values = Set.union values Set.empty

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
