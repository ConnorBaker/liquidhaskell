module DefaultStimesGood where

data Box = Box Bool

instance Semigroup Box where
    _ <> right = right
