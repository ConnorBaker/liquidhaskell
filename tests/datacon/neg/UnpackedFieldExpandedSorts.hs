{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The GUARD for @pos/UnpackedFieldExpandedSorts.hs@, and NOT its attribution
-- -- before the fix this module also failed, with @Illegal type
-- specification@, so @--expect-any-error@ would have been discharged by the
-- very defect the positive exists to catch. It pins @Liquid Type Mismatch@ for
-- that reason.
--
-- What it holds down is that answering 'resortedFields' per EXPANSION did not
-- buy the extra provability for free. Dropping a selector removes equations
-- rather than adding them, so the risk runs the other way -- but the fix also
-- changes WHICH equations are emitted for the fields that remain, and this is
-- the arm that says a false claim about one of them is still rejected.
module UnpackedFieldExpandedSorts where

import Data.IORef (IORef)

data Extent = Extent !Int !Int

data T = T !(IORef Int) {-# UNPACK #-} !Extent

{-@ measure widthOf @-}
widthOf :: T -> Int
widthOf (T _ (Extent w _)) = w

-- Claims the WIDTH and stores the HEIGHT.
{-@ mkT :: r:(IORef Int) -> w:Int -> h:Int -> {v:T | widthOf v == w} @-}
mkT :: IORef Int -> Int -> Int -> T
mkT r w h = T r (Extent h w)
