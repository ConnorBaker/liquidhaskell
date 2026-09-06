{-# OPTIONS_GHC -O1 #-}

-- | A measure equation is lifted from GHC's Core, which is written over a data
-- constructor's REPRESENTATION arguments; the logic knows the constructor by
-- its SOURCE fields. From @-O1@ up those are not the same list.
--
-- @-funbox-small-strict-fields@ replaces a strict field whose type is a
-- single-constructor product by that product's own arguments, so the record
-- selector for @proofWitness@ below is compiled to
--
-- > proofWitness = \p -> case p of Proof _ s -> Witness s
--
-- where @s@ is the unpacked @Set Int@ and @Witness s@ REBUILDS the field.
-- Binding @s@ at the source field's type @Witness@ -- which is what the logic
-- declares @Proof@ to take -- makes that body the ill-sorted @Witness (s ::
-- Witness)@. Before the fix this module got no verdict at all: @Bad Measure
-- Specification@ on the measure and @Illegal type specification for
-- `Proof`@/@`$WProof`@ on the declaration, none of them naming the field.
--
-- Note the two directions have to agree. The equation is rebuilt over the
-- source fields for the WRAPPER, by projecting each component out of the field
-- it came from; and back over the representation arguments for the WORKER,
-- which really does take them. 'mkProof' is eta-reduced so it goes through the
-- wrapper, and 'pairProof' applies the constructor so it goes through the
-- worker; both must hold.
--
-- @Set Int@ is load bearing in a way @Int@ would not be: an EMBEDDED type has
-- no constructor in the logic to rebuild it with, so the expansion has to stop
-- at one and descend through the other. @tests/datacon/pos/UnpackedFieldSorts@
-- covers the stopping case.
module UnpackedFieldRebuild where

import Data.Set (Set)

data Witness = Witness { witnessKeys :: !(Set Int) }

{-@ measure witnessKeys @-}

data Proof = Proof
  { proofOrdinal :: !Int
  , proofWitness :: !Witness
  }

{-@ measure proofOrdinal @-}
{-@ measure proofWitness @-}

{-@ mkProof :: n:Int -> w:Witness -> {v:Proof | proofOrdinal v == n && proofWitness v == w} @-}
mkProof :: Int -> Witness -> Proof
mkProof = Proof

{-@ pairProof :: n:Int -> w:Witness -> {v:Proof | proofWitness v == w} @-}
pairProof :: Int -> Witness -> Proof
pairProof n w = Proof n w
