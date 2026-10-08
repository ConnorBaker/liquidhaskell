{-# LANGUAGE AllowAmbiguousTypes #-}

module BoundEvidenceBad where

import Data.Coerce (Coercible, coerce)

castVia :: forall a b. (Coercible a b) => a -> b
castVia = coerce
{-# NOINLINE castVia #-}

{-@ rebox :: forall a. Coercible a Nat => Int -> a @-}
rebox :: forall a. (Coercible a Int) => Int -> a
rebox value = castVia @Int @a value
{-# NOINLINE rebox #-}
