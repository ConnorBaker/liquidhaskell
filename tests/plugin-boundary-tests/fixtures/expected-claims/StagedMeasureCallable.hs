module StagedMeasureCallable where

import Data.Set (Set)
import qualified Data.Set as Set

data Witness = Witness {candidates :: !(Set Integer)}

{-@ measure candidates @-}
{-@ reflect witnessUnion @-}
{-@ witnessUnion :: left:Witness -> right:Witness
      -> {v:Witness | candidates v == Set_cup (candidates left) (candidates right)} @-}
witnessUnion :: Witness -> Witness -> Witness
witnessUnion left right = Witness (Set.union (candidates left) (candidates right))

{-@ instance Semigroup Witness where
      (<>) :: left:Witness -> right:Witness
          -> {v:Witness | candidates v == Set_cup (candidates left) (candidates right)} @-}
instance Semigroup Witness where
    (<>) = witnessUnion
