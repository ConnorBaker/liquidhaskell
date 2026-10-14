-- A derived instance has no method contracts: its max may return any K, so
-- the dictionary keeps the class constructor's field variance.
module SetUnionDerivedOrd (K (..), combine) where

import qualified Data.Set as Set

data K = K Int deriving (Eq, Ord)

{-@ measure kv @-}
kv :: K -> Int
kv (K n) = n

{-@ combine :: Set.Set {k:K | kv k > 0} -> Set.Set {k:K | kv k > 0} -> Set.Set {k:K | kv k > 0} @-}
combine :: Set.Set K -> Set.Set K -> Set.Set K
combine a b = Set.union a b
