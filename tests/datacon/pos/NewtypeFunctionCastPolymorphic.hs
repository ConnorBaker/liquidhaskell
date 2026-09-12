{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}

{-# LANGUAGE RankNTypes #-}
module NewtypeFunctionCastPolymorphic (Box (..), adapt) where

newtype Box a = Box [a]

adapt :: (forall a. Box a -> [a]) -> (forall a. [a] -> [a])
adapt function entries = function (Box entries)

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
