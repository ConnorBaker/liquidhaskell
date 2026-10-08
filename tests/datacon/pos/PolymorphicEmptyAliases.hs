{-# OPTIONS_GHC -O2 #-}

{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module PolymorphicEmptyAliases (
    Token (..),
    emptyLocal,
    localTokens,
    localInts,
    nothingToken,
    nothingInt,
    keepTokens,
    keepLaw,
) where

import qualified Data.Set as Set

data Token = First | Second
    deriving (Eq, Ord)

-- Keep a genuine polymorphic alias visible through optimized Core.
{-# NOINLINE emptyLocal #-}
{-@ emptyLocal :: {v:Set.Set a | Set_emp v} @-}
emptyLocal :: Set.Set a
emptyLocal = Set.empty

{-@ localTokens :: () -> {v:Set.Set Token | Set_emp v} @-}
localTokens :: () -> Set.Set Token
localTokens () = emptyLocal

{-@ localInts :: () -> {v:Set.Set Int | Set_emp v} @-}
localInts :: () -> Set.Set Int
localInts () = emptyLocal

{-@ nothingToken :: () -> {v:Maybe Token | v == Nothing} @-}
nothingToken :: () -> Maybe Token
nothingToken () = Nothing

{-@ nothingInt :: () -> {v:Maybe Int | v == Nothing} @-}
nothingInt :: () -> Maybe Int
nothingInt () = Nothing

{-@ reflect keepTokens @-}
{-@ keepTokens :: values:Set.Set Token -> {v:Set.Set Token | v == values} @-}
keepTokens :: Set.Set Token -> Set.Set Token
keepTokens values = Set.union values emptyLocal

{-@ keepLaw :: values:Set.Set Token -> {keepTokens values == values} @-}
keepLaw :: Set.Set Token -> ()
keepLaw values = keepTokens values `seq` ()

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
