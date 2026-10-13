module EmbeddingOwner where

import Data.Set (Set)

data Evidence = Evidence
type EvidenceAlias = Evidence
type ContainerAlias a = Set a
type NonPrefixAlias a = (a, Int)
type RepeatedAlias a = (a, a)
type IdentityAlias a = a
type ConstantAlias a = Bool
data ActionA a = ActionA a
data ActionB a = ActionB a
newtype Provenance = Provenance (Set Evidence)
