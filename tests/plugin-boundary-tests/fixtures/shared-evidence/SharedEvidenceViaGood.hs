{-# LANGUAGE DerivingVia #-}

module SharedEvidenceViaGood (V (..)) where

-- A deriving-via instance of a refined class.
newtype V = V [Int]
  deriving (Semigroup) via [Int]
