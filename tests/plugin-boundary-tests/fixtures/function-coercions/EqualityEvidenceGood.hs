{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}

module EqualityEvidenceGood where

import Data.Coerce (Coercible, coerce)

representational :: forall a b. (Coercible a b) => a -> b
representational = coerce

nominal :: forall a b. (a ~ b) => a -> b
nominal value = value

{-@ preserveRepresentational :: Nat -> Nat @-}
preserveRepresentational :: Int -> Int
preserveRepresentational = representational @Int @Int

{-@ preserveNominal :: Nat -> Nat @-}
preserveNominal :: Int -> Int
preserveNominal = nominal @Int @Int

{-@ weaken :: Nat -> Int @-}
weaken :: Int -> Int
weaken = representational @Int @Int
