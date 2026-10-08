{-# LANGUAGE AllowAmbiguousTypes #-}

module BoundDirectBad where

import Data.Coerce (Coercible, coerce)

{-@ direct :: forall a. Coercible a Nat => Int -> a @-}
direct :: forall a. (Coercible a Int) => Int -> a
direct = coerce
{-# NOINLINE direct #-}
