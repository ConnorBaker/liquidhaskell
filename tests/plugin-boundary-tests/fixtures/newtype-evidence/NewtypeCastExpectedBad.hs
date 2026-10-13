module NewtypeCastExpectedBad where

import qualified Data.Set as Set

-- A newtype constructor application is a Core cast. Its expected refinement
-- is an obligation, never a premise of the cast it checks.
newtype Positive = Positive Int
newtype Members = Members (Set.Set Int)

{-@ forged :: Int -> {p:Positive | false} @-}
forged :: Int -> Positive
forged value = Positive value

{-@ emptyMembers :: {m:Members | false} @-}
emptyMembers :: Members
emptyMembers = Members Set.empty
