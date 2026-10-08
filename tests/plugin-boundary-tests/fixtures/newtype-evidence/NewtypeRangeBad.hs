{-# LANGUAGE AllowAmbiguousTypes #-}

module NewtypeRangeBad where

import Data.Coerce (Coercible, coerce)

{-@ data Positive = Positive { positive :: Nat } @-}
newtype Positive = Positive {positive :: Int}

castVia :: forall a b. (Coercible a b) => a -> b
castVia = coerce
{-# NOINLINE castVia #-}

{-@ forgeRange :: Nat -> {p:Positive | positive p > 10} @-}
forgeRange :: Int -> Positive
forgeRange = castVia @Int @Positive
