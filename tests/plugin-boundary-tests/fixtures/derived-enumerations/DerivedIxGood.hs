module DerivedIxGood (Slot (..), slots) where

import Data.Ix (Ix, range)

data Slot = Low | Mid | High
  deriving stock (Eq, Ord, Ix, Show)

slots :: [Slot]
slots = range (Low, High)
