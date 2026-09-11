{-# LANGUAGE MagicHash, GADTs #-}
{-@ LIQUID "--total-Haskell" @-}
module DataToTagRepresentation where

import GHC.Exts (Int(I#))
import GHC.Prim (dataToTagSmall#, dataToTagLarge#)

data Indexed a where
  IndexedInt :: Int -> Indexed Int
  IndexedBool :: Bool -> Indexed Bool

-- Without a corresponding logical ADT declaration, the primitive remains
-- unconstrained. GHC validity alone must not invent logical constructor tests.
{-@ fail unsupportedIndexed @-}
{-@ unsupportedIndexed :: Indexed a -> {v:Int | 0 <= v && v < 2} @-}
unsupportedIndexed :: Indexed a -> Int
unsupportedIndexed x = I# (dataToTagSmall# x)

-- These boxed types have numeric logical representations, not constructor
-- ADTs. Calling a tag primitive must not make their contexts inconsistent.
{-@ fail wrongIntTag @-}
{-@ wrongIntTag :: Int -> {v:Int | v == 1} @-}
wrongIntTag :: Int -> Int
wrongIntTag x = I# (dataToTagSmall# x)

{-@ fail wrongIntegerTag @-}
{-@ wrongIntegerTag :: Integer -> {v:Int | v == 3} @-}
wrongIntegerTag :: Integer -> Int
wrongIntegerTag x = I# (dataToTagLarge# x)

{-@ fail _lhVacuityProbe @-}
{-@ _lhVacuityProbe :: Int -> {v:Int | v > 0} @-}
_lhVacuityProbe :: Int -> Int
_lhVacuityProbe x = x - 1
