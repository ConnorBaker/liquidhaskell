module ProvenanceEmbeddingWrongType where

import Data.Set qualified as Set
import NominalEvidence qualified
import OtherEvidence qualified

{-@ embed Provenance as (Set_Set NominalEvidence.Evidence) @-}
newtype Provenance = Provenance (Set.Set NominalEvidence.Evidence)

{-@ wrap :: atoms:Set.Set OtherEvidence.Evidence -> {v:Provenance | v == atoms} @-}
wrap :: Set.Set OtherEvidence.Evidence -> Provenance
wrap _ = Provenance Set.empty
