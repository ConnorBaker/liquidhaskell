module ProvenanceEmbeddingPrimitive where

import Data.Set qualified as Set

{-@ embed Provenance as (Set_Set int) @-}
newtype Provenance = Provenance (Set.Set Integer)

{-@ wrap :: atoms:Set.Set Integer -> {v:Provenance | v == atoms} @-}
wrap :: Set.Set Integer -> Provenance
wrap = Provenance
