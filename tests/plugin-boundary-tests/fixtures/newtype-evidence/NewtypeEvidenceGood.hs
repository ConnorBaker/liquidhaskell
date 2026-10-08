{-# LANGUAGE AllowAmbiguousTypes #-}

module NewtypeEvidenceGood where

import Data.Coerce (Coercible, coerce)

{-@ data Positive = Positive { positive :: Nat } @-}
newtype Positive = Positive {positive :: Int}

castVia :: forall a b. (Coercible a b) => a -> b
castVia = coerce
{-# NOINLINE castVia #-}

{-@ construct :: Nat -> Positive @-}
construct :: Int -> Positive
construct = castVia @Int @Positive

{-@ aboveTen :: {x:Int | x > 10} -> {p:Positive | positive p > 10} @-}
aboveTen :: Int -> Positive
aboveTen = castVia @Int @Positive

{-@ project :: Positive -> Nat @-}
project :: Positive -> Int
project = castVia @Positive @Int

{-@ inhabited :: Nat @-}
inhabited :: Int
inhabited = project (aboveTen 11)
