module AssumptionClientBad where

import AssumptionProducer (lookupRows, trusted)
import Data.Map.Strict (Map)

{-@ checked :: Ord a => m:Map a Int -> k:a -> {v:Maybe Int | v /= lookupRows m k} @-}
checked :: (Ord a) => Map a Int -> a -> Maybe Int
checked = trusted
