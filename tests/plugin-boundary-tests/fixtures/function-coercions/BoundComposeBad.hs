{-# LANGUAGE AllowAmbiguousTypes #-}

module BoundComposeBad where

import Data.Coerce (Coercible, coerce)

{-@ compose :: forall a b. (Coercible a b, Coercible b Nat) => Int -> a @-}
compose :: forall a b. (Coercible a b, Coercible b Int) => Int -> a
compose = coerce
{-# NOINLINE compose #-}
