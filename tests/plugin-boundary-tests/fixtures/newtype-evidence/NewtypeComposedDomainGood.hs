module NewtypeComposedDomainGood where

import Data.Coerce (coerce)

{-@ data Inner a = Inner { items :: {v:[a] | 0 < len v} } @-}
newtype Inner a = Inner {items :: [a]}

newtype Outer a = Outer (Inner a)

{-@ admit :: {entries:[Int] | 0 < len entries} -> Outer Int @-}
admit :: [Int] -> Outer Int
admit = coerce

{-@ release :: Outer Int -> {entries:[Int] | 0 < len entries} @-}
release :: Outer Int -> [Int]
release = coerce
