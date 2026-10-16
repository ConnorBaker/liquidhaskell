module SharedEvidenceNewtypeNFDataGood (R (..)) where

import Control.DeepSeq (NFData)

-- Two newtype-derived instances in one clause (Relation.hs's shape).
newtype R = R [Int]
  deriving newtype (NFData, Semigroup)
