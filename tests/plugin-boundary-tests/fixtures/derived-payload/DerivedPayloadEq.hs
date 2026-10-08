module DerivedPayloadEq where

data Domain = DomainA !Bool !Integer | DomainB !Integer !Bool deriving (Eq)
