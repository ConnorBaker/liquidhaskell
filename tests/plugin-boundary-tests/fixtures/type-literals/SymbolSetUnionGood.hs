{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}

module SymbolSetUnionGood where

import Data.Set (Set)
import qualified Data.Set as Set
import GHC.TypeLits (Symbol)

type role TextId nominal
newtype TextId (domain :: Symbol) = TextId Int deriving (Eq, Ord)
type CandidateKey = TextId "candidate_key"
data Witness = Witness {candidates :: Set CandidateKey}

{-@ measure candidates @-}

{-@ unite :: left:Witness -> right:Witness
      -> {v:Witness | candidates v == Set_cup (candidates left) (candidates right)} @-}
unite :: Witness -> Witness -> Witness
unite left right = Witness (Set.union (candidates left) (candidates right))
