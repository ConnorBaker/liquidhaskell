{-# LANGUAGE NoImplicitPrelude #-}
module NaturalUnitWorkerBad (quotient) where

import GHC.Num.Natural (Natural, naturalQuot)

{-@ quotient :: Natural -> Natural -> Natural @-}
quotient :: Natural -> Natural -> Natural
quotient x y = naturalQuot x y
