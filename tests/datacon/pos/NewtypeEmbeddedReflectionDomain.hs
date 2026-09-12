{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module NewtypeEmbeddedReflectionDomain (Support, wrap, unwrap, roundtrip) where
import Data.Coerce (coerce)
import Data.Set qualified as Set

{-@ embed Support as (Set_Set int) @-}
{-@ newtype Support = Support { stored :: {v:Set.Set Int | not (Set_emp v)} } @-}
newtype Support = Support { stored :: Set.Set Int }

{-@ wrap :: entries:{v:Set.Set Int | not (Set_emp v)} -> {v:Support | v == entries} @-}
wrap :: Set.Set Int -> Support
wrap = Support

{-@ unwrap :: support:Support -> {v:Set.Set Int | v == support && not (Set_emp v)} @-}
unwrap :: Support -> Set.Set Int
unwrap = coerce

{-@ roundtrip :: entries:{v:Set.Set Int | not (Set_emp v)} -> {v:Set.Set Int | v == entries} @-}
roundtrip :: Set.Set Int -> Set.Set Int
roundtrip entries = unwrap (wrap entries)

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
