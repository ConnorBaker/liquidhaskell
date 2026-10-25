module RefinedConsumerFalse where

import RefinedDependent
import RefinedOwner

-- Relies on R's refined field, which only RefinedOwner's declaration states.
{-@ nonneg :: r:R -> {v:Int | 0 < v} @-}
nonneg :: R -> Int
nonneg (R n) = n
