{-# LANGUAGE NoImplicitPrelude #-}

{-@ LIQUID "--rankNTypes" @-}
module ImportedInstanceCallbackWideGood where

import GHC.Types (Int)
import ImportedCallbackCarrier (Apply (..))

-- The class offers only predicate-preserving callbacks. This actual instance
-- accepts arbitrary callbacks, a wider callable domain, so it is compatible.
{-@ class Apply a where
      applyCallback :: (forall <p :: a -> Bool>. a<p> -> a<p>) -> a -> a @-}
{-@ instance Apply Int where
      assume applyCallback :: (Int -> Int) -> Int -> Int @-}

{-@ raw :: Int -> Int @-}
raw :: Int -> Int
raw value = applyCallback (\input -> input) value
