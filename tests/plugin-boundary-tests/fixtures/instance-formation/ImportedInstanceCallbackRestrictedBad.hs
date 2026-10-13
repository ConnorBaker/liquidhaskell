{-# LANGUAGE NoImplicitPrelude #-}

{-@ LIQUID "--rankNTypes" @-}
module ImportedInstanceCallbackRestrictedBad where

import GHC.Types (Int)
import ImportedCallbackCarrier (Apply (..))

-- The raw class permits callbacks that change values, such as const 0.
-- The authored instance cannot require every caller's callback to preserve
-- every predicate: a method argument reverses the subtype direction.
{-@ class Apply a where
      applyCallback :: (a -> a) -> a -> a @-}
{-@ instance Apply Int where
      assume applyCallback :: (forall <p :: Int -> Bool>. Int<p> -> Int<p>) -> Int -> Int @-}

ordinary :: Int -> Int
ordinary value = value
