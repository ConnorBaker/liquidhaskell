{-# LANGUAGE AllowAmbiguousTypes #-}

module NewtypeEvidenceBad where

import Data.Coerce (Coercible, coerce)

{-@ data Positive = Positive { positive :: Nat } @-}
newtype Positive = Positive {positive :: Int}

castVia :: forall a b. (Coercible a b) => a -> b
castVia = coerce
{-# NOINLINE castVia #-}

{-@ construct :: Int -> Positive @-}
construct :: Int -> Positive
construct = castVia @Int @Positive
