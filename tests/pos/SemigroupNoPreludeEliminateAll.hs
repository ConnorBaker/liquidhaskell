{-# LANGUAGE NoImplicitPrelude #-}

{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--eliminate=all" @-}
module SemigroupNoPreludeEliminateAll where

import GHC.Base (Semigroup (..))
import GHC.Types (Int)

data Unit = Unit

instance Semigroup Unit where
    Unit <> Unit = Unit

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x
