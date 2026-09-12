{-# OPTIONS_GHC -O2 #-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

module NewtypeCastGeneric (Nonempty (..), invalid) where

import GHC.Generics (Generic (to), M1 (M1), K1 (K1))

{-@ newtype Nonempty a = Nonempty { items :: {v:[a] | len v > 0} } @-}
newtype Nonempty a = Nonempty { items :: [a] }
  deriving stock (Generic)

invalid :: () -> Nonempty Int
invalid () = to (M1 (M1 (M1 (K1 []))))

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
