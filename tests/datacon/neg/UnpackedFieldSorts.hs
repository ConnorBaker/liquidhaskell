{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The negative half of @tests/datacon/pos/UnpackedFieldSorts.hs@: the field
-- whose sort SURVIVES unpacking is still CHECKED, not merely well-sorted.
--
-- @--expect-error-containing@ rather than @--expect-any-error@, for the reason
-- the sibling @UnpackedFieldBinders@ modules record: before the fix this
-- module also failed, with @Illegal type specification@ raised on the data
-- declaration, so the weaker form was discharged by the very defect the
-- positive exists to catch and passed while proving nothing.
module UnpackedFieldSorts where

import Data.IORef (IORef)

data T = T
  { ta :: !(IORef Int)
  , tb :: !Int
  }

{-@ measure tb @-}

-- FALSE: 'mkT' stores @n@, not @n + 1@.
{-@ mkT :: r:(IORef Int) -> n:Int -> {v:T | tb v == n + 1} @-}
mkT :: IORef Int -> Int -> T
mkT = T
