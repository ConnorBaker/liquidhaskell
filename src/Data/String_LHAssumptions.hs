{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}

module Data.String_LHAssumptions where

import Data.String
import GHC.Types_LHAssumptions ()

{-@
measure stringlen :: a -> Int

// A runtime IsString dictionary may map every input to the same value.
class IsString a where
    fromString :: [Char] -> a

// The native String instance is identity; this is not a class law.
instance IsString ([Char]) where
    assume fromString :: i:[Char] -> {o:[Char] | o = i}
@-}
