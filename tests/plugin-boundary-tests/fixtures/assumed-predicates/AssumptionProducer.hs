module AssumptionProducer where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

{-@ opaque-reflect lookupRows @-}
lookupRows :: (Ord a) => Map a b -> a -> Maybe b
lookupRows m k = Map.lookup k m

{-@ assume trusted :: Ord a => m:Map a Int -> k:a -> {v:Maybe Int | v == lookupRows m k} @-}
trusted :: (Ord a) => Map a Int -> a -> Maybe Int
trusted = lookupRows

{-@ assume Map.lookup :: Ord a => k:a -> m:Map a b -> {v:Maybe b | v == lookupRows m k} @-}

{-@ checked :: Ord a => m:Map a Int -> k:a -> {v:Maybe Int | v == lookupRows m k} @-}
checked :: (Ord a) => Map a Int -> a -> Maybe Int
checked = trusted
