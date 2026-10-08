{-# LANGUAGE AllowAmbiguousTypes #-}

module NewtypeProjectionBad where

import Data.Coerce (Coercible, coerce)

{-@ data Positive = Positive { positive :: Nat } @-}
newtype Positive = Positive {positive :: Int}

castVia :: forall a b. (Coercible a b) => a -> b
castVia = coerce
{-# NOINLINE castVia #-}

{-@ forgeProjection :: Positive -> {v:Int | v > 10} @-}
forgeProjection :: Positive -> Int
forgeProjection = castVia @Positive @Int
