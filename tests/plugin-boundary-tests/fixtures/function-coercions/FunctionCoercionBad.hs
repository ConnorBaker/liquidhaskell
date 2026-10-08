{-# LANGUAGE ScopedTypeVariables #-}

module FunctionCoercionBad where

import Data.Coerce (Coercible, coerce)

{-@ transport :: (Nat -> a) -> Int -> b @-}
transport :: forall a b. (Coercible a b) => (Int -> a) -> Int -> b
transport function = coerce function
{-# NOINLINE transport #-}
