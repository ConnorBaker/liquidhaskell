{-# OPTIONS_GHC -O2 #-}

{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

module PolymorphicNestedWrong (Token (..), keep, wrapped, wrappedIdentity) where

import qualified Data.Set as Set

data Token = First | Second
    deriving (Eq, Ord)

{-# NOINLINE keep #-}
{-@ reflect keep @-}
keep :: Set.Set a -> [a] -> Set.Set a
keep values _ = values

{-# NOINLINE wrapped #-}
{-@ reflect wrapped @-}
wrapped :: Token -> Set.Set Token
wrapped _ = keep (Set.singleton First) []

{-@ wrappedIdentity :: token:Token -> {wrapped token == Set.empty} @-}
wrappedIdentity :: Token -> ()
wrappedIdentity _ = ()

{-@ fail wrongMember @-}
{-@ wrongMember :: token:Token -> {v:Bool | v} @-}
wrongMember :: Token -> Bool
wrongMember token = Set.member token (wrapped token)

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
