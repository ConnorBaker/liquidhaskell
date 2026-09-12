{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module NewtypeEmbeddedReflectionClient (forceImportedUnion) where
import NewtypeEmbeddedReflectionSource (Support, unionSupport)

{-@ forceImportedUnion :: support:Support -> {unionSupport support support == support} @-}
forceImportedUnion :: Support -> ()
forceImportedUnion support = unionSupport support support `seq` ()

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
