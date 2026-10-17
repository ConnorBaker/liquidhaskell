module DerivedEnumGood (Colour (..), allColours) where

data Colour = Red | Green | Blue
  deriving stock (Bounded, Enum, Eq, Ord, Show)

allColours :: [Colour]
allColours = [minBound .. maxBound]
