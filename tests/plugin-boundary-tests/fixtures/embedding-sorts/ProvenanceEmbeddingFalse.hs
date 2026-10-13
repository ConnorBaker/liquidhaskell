module ProvenanceEmbeddingFalse where

import Data.Set qualified as Set
import NominalEvidence qualified

{-@ embed Provenance as (Set_Set NominalEvidence.Evidence) @-}
newtype Provenance = Provenance (Set.Set NominalEvidence.Evidence)

{-@ wrap :: atoms:Set.Set NominalEvidence.Evidence -> {v:Provenance | v == atoms} @-}
wrap :: Set.Set NominalEvidence.Evidence -> Provenance
wrap _ = Provenance Set.empty
