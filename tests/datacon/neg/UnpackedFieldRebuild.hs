{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The negative half of @tests/datacon/pos/UnpackedFieldRebuild.hs@: the
-- rebuilt equation is CHECKED, not merely well-sorted.
--
-- @--expect-error-containing@ rather than @--expect-any-error@: before the fix
-- this module failed too, with @Illegal type specification@ on the data
-- declaration, so the weaker form was discharged by the defect the positive
-- exists to catch.
module UnpackedFieldRebuild where

import Data.Set (Set)

data Witness = Witness { witnessKeys :: !(Set Int) }

{-@ measure witnessKeys @-}

data Proof = Proof
  { proofOrdinal :: !Int
  , proofWitness :: !Witness
  }

{-@ measure proofWitness @-}

-- FALSE: 'mkProof' stores @w@, so its witness cannot differ from @w@'s.
{-@ mkProof :: n:Int -> w:Witness
            -> {v:Proof | proofWitness v == w
                       && witnessKeys (proofWitness v) /= witnessKeys w} @-}
mkProof :: Int -> Witness -> Proof
mkProof = Proof
