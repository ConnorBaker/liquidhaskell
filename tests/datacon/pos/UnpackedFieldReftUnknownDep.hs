{-# OPTIONS_GHC -O1 #-}
-- A DEPENDENT refinement between two strict fields the logic has no datatype
-- for: both @IORef Int@ fields unpack to a @MutVar#@ leaf that stands in for
-- its field (see @UnpackedFieldReftUnknown.hs@), and @b2@'s refinement names
-- @b1@. The sibling branch of 'RefType.expandOver' keeps @b1@ as the binder
-- rather than substituting a rebuild for it, so @v == b1@ is stated over the
-- two leaves: well sorted, since both sit at the same leaf sort, and meaning
-- what it meant over the fields, since the newtype chain is injective.
--
-- This is where the series is strictly MORE permissive than its base:
-- lh/integration (41c6c09b4) rebuilt through the chain and reported
-- @Unbound symbol GHC.Internal.STRef.STRef@ for this module (reviewer's
-- measurement, 2026-09-09); here it is SAFE (2). The obligation is real:
-- 'mk' passes the same reference twice.
module UnpackedFieldReftUnknownDep where

import Data.IORef

data B = B !(IORef Int) !(IORef Int) !Int

{-@ data B = B (b1 :: IORef Int) (b2 :: {v:IORef Int | v == b1}) (bN :: Int) @-}

{-@ mk :: r:IORef Int -> n:Int -> {v:B | bN v == n} @-}
mk :: IORef Int -> Int -> B
mk r n = B r r n
