{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}

module EqualityEvidenceBad where

import Data.Coerce (Coercible, coerce)

representational :: forall a b. (Coercible a b) => a -> b
representational = coerce

nominal :: forall a b. (a ~ b) => a -> b
nominal value = value

{-@ forgeRepresentational :: Int -> Nat @-}
forgeRepresentational :: Int -> Int
forgeRepresentational = representational @Int @Int

{-@ forgeNominal :: Int -> Nat @-}
forgeNominal :: Int -> Int
forgeNominal = nominal @Int @Int
