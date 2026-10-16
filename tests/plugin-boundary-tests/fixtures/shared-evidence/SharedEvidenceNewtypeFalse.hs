module SharedEvidenceNewtypeFalse (L (..), joinedLength) where

newtype L = L [Int]
  deriving newtype (Semigroup)

-- The derived append is checked through the instance: joining two lists need
-- not produce a nonempty one.
{-@ joinedLength :: L -> L -> {v:Int | v > 0} @-}
joinedLength :: L -> L -> Int
joinedLength x y = case x <> y of
  L zs -> length zs
