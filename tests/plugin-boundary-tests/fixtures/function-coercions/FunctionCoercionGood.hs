{-# LANGUAGE ScopedTypeVariables #-}

module FunctionCoercionGood where

import Data.Coerce (Coercible, coerce)

{-@ transport :: (Nat -> a) -> Nat -> b @-}
transport :: forall a b. (Coercible a b) => (Int -> a) -> Int -> b
transport function = coerce function
{-# NOINLINE transport #-}
