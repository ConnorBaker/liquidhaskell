module GeneratedDictionaryNestedBad where

-- A refined instance head makes every Int argument an obligation.
class Positive a where
    positive :: a -> Bool

{-@ instance Positive ({v:Int | v > 0}) where
      positive :: {v:Int | v > 0} -> Bool @-}
instance Positive Int where
    positive _ = True

instance (Positive a) => Positive [a] where
    positive = all positive

-- The Positive [Int] dictionary is used only by the generated Positive [[Int]]
-- dictionary, which this use demands.
anyPositive :: [[Int]] -> Bool
anyPositive xs = positive xs
