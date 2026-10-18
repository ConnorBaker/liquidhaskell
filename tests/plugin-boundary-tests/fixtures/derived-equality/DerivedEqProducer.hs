module DerivedEqProducer (Color (..), Pair (..)) where

data Color = Red | Green | Blue deriving (Eq)

data Pair = Pair Color Integer deriving (Eq)
