{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module NewtypeEmbeddedReflectionDomainBad (Support, wrapAny) where
import Data.Set qualified as Set

{-@ embed Support as (Set_Set int) @-}
{-@ newtype Support = Support { stored :: {v:Set.Set Int | not (Set_emp v)} } @-}
newtype Support = Support { stored :: Set.Set Int }

wrapAny :: Set.Set Int -> Support
wrapAny entries = Support entries

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
