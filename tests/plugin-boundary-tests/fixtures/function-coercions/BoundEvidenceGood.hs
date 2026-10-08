{-# LANGUAGE AllowAmbiguousTypes #-}

module BoundEvidenceGood where

import Data.Coerce (Coercible, coerce)

castVia :: forall a b. (Coercible a b) => a -> b
castVia = coerce
{-# NOINLINE castVia #-}

{-@ rebox :: forall a. Coercible a Nat => Nat -> a @-}
rebox :: forall a. (Coercible a Int) => Int -> a
rebox value = castVia @Int @a value
{-# NOINLINE rebox #-}

{-@ direct :: forall a. Coercible a Nat => Nat -> a @-}
direct :: forall a. (Coercible a Int) => Int -> a
direct = coerce
{-# NOINLINE direct #-}

{-@ compose :: forall a b. (Coercible a b, Coercible b Nat) => Nat -> a @-}
compose :: forall a b. (Coercible a b, Coercible b Int) => Int -> a
compose = coerce
{-# NOINLINE compose #-}

{-@ inhabited :: (Nat, Nat, Nat) @-}
inhabited :: (Int, Int, Int)
inhabited = (rebox @Int 1, direct @Int 1, compose @Int @Int 1)
