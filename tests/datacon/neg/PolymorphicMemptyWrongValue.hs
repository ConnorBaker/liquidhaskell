{-# OPTIONS_GHC -O2 #-}

{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--no-annotations" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

module PolymorphicMemptyWrongValue (Box (..), takeBox, fromDefault, retainsDefault, wrongDefault) where

data Box = Box Int
    deriving (Eq)

instance Semigroup Box where
    Box left <> Box right = Box (left + right)

instance Monoid Box where
    mempty = Box 0

-- Transport the same instance of the actual class method. Its implementation
-- is opaque here: this is not an assumed equation mempty == Box 0.
{-@ opaque-reflect mempty @-}

{-# NOINLINE takeBox #-}
{-@ reflect takeBox @-}
takeBox :: Box -> Box
takeBox box = box

{-@ reflect fromDefault @-}
fromDefault :: () -> Box
fromDefault () = takeBox mempty

{-@ retainsDefault :: argument:() -> {fromDefault argument == mempty} @-}
retainsDefault :: () -> ()
retainsDefault _ = ()

{-@ wrongDefault :: argument:() -> {fromDefault argument == Box 1} @-}
wrongDefault :: () -> ()
wrongDefault _ = ()

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | 0 < v} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe argument = argument - 1
