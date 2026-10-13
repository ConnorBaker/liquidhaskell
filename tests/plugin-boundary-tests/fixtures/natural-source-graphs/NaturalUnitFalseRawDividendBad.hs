{-# LANGUAGE NoImplicitPrelude #-}
module NaturalUnitFalseRawDividendBad (nativeUnit) where

import GHC.Classes ((==))
import GHC.Num (fromInteger)
import GHC.Num.Natural (Natural)
import GHC.Types (Bool)

{-@ nativeUnit :: x:Natural -> y:Natural -> {b:Bool | b => naturalCheck x} @-}
nativeUnit :: Natural -> Natural -> Bool
nativeUnit _ y = y == (fromInteger 1 :: Natural)
