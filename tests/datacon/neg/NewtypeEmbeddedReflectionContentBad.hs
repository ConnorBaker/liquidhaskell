{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module NewtypeEmbeddedReflectionContentBad (Support, discard) where
import Data.Set qualified as Set

{-@ embed Support as (Set_Set int) @-}
newtype Support = Support (Set.Set Int)

{-@ discard :: support:Support -> {v:Set.Set Int | v == support} @-}
discard :: Support -> Set.Set Int
discard _ = Set.empty

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
