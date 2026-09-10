{-# LANGUAGE NoImplicitPrelude #-}

{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}

module SemigroupNoPrelude where

import GHC.Base (Semigroup (..))
import GHC.Num (fromInteger)
import GHC.Types (Int)

data Unit = Unit

instance Semigroup Unit where
    Unit <> Unit = Unit

validCall :: Unit
validCall = stimes (1 :: Int) Unit

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x
