module SharedEvidenceNewtypeGood (L (..)) where

-- A newtype-derived instance of a refined class: its dictionary function's
-- construction is closed, so it must stay that instance's own construction
-- rather than become an alias of shared evidence.
newtype L = L [Int]
  deriving newtype (Semigroup)
