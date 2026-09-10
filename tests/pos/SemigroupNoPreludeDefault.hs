{-# LANGUAGE NoImplicitPrelude #-}

{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module SemigroupNoPreludeDefault where

import GHC.Base (Semigroup (..))
import GHC.Types (Int)

data Unit = Unit

-- No numeric imports or user-written literals: the default itself requires
-- both comparison and fromInteger specifications for its positive guard.
instance Semigroup Unit where
    Unit <> Unit = Unit

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x
