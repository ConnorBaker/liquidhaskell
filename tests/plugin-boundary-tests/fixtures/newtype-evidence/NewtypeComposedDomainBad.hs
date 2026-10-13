module NewtypeComposedDomainBad where

import Data.Coerce (coerce)

{-@ data Inner a = Inner { items :: {v:[a] | 0 < len v} } @-}
newtype Inner a = Inner {items :: [a]}

newtype Outer a = Outer (Inner a)

-- Reaching Outer from a list crosses Inner's refined field. A composed
-- coercion must not hide that intermediate boundary.
bypass :: [Int] -> Outer Int
bypass = coerce
