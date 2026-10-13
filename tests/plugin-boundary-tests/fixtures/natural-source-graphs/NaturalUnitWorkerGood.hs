{-# LANGUAGE NoImplicitPrelude #-}
module NaturalUnitWorkerGood (quotient) where

import GHC.Maybe (Maybe (..))
import GHC.Num.Natural (Natural, naturalQuot)
import NaturalUnitProducer (nativeUnit)

{-@ quotient :: Natural -> Natural -> Maybe Natural @-}
quotient :: Natural -> Natural -> Maybe Natural
quotient x y = if nativeUnit x y then Just (naturalQuot x y) else Nothing
