module GeneratedDictionaryBad where

-- A refined instance head makes every Int argument an obligation.
class Positive a where
    positive :: a -> Bool

{-@ instance Positive ({v:Int | v > 0}) where
      positive :: {v:Int | v > 0} -> Bool @-}
instance Positive Int where
    positive _ = True

instance (Positive a) => Positive [a] where
    positive = all positive

-- GHC binds the Positive [Int] dictionary as a generated top-level binder.
-- Its obligation on the refined Int instance belongs to this use.
anyPositive :: [Int] -> Bool
anyPositive xs = positive xs
