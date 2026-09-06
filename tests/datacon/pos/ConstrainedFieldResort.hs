{-# OPTIONS_GHC -O1 #-}
{-# LANGUAGE GADTs #-}

-- | A CONSTRAINED constructor one of whose fields changes sort when unpacked.
--
-- This is the shape `ConstrainedFieldSorts` was written for, and it exists
-- because that module stopped reading on the fix it was written for.
--
-- The fix is the dictionary skip: `dataConRepArgTys` leads with one argument
-- per class constraint and `dataConOrigArgTys` carries none, so comparing the
-- two head to head lines a constrained constructor's one FIELD up against its
-- DICTIONARY, decides the sort has changed, drops the selector and rejects the
-- declaration with `Illegal type specification`.
--
-- Reaching that comparison at all needs a field whose sort really can move,
-- which means a field the expansion actually descends into. `Keys` wraps a
-- `Set`, so unpacking rewrites it to an SMT array. `ConstrainedFieldSorts` has
-- no such field: once expansion was restricted to what
-- `-funbox-small-strict-fields` actually unpacks, nothing about it reaches the
-- misalignment any more. Measured on the final tree, disarming the dictionary
-- skip leaves that module at SAFE (0 constraints checked) and moves this one
-- from SAFE (1 constraints checked) to `Illegal type specification`.
--
-- `Keyed` must be a `data` and not a `newtype`, for the reason
-- `ConstrainedFieldSorts` records: a newtype is erased and nothing unpacks, so
-- the newtype spelling is accepted before the fix and proves nothing.
module ConstrainedFieldResort where

import Data.Set (Set)

class Rel row where
  relKey :: row -> Int

data Keys = Keys (Set Int)

data Keyed row where
  Keyed :: (Rel row) => { keyedOrdinal :: !Int, keyedKeys :: !Keys } -> Keyed row

{-@ measure keyedOrdinal @-}

{-@ mkKeyed :: n:Int -> {v:Keyed row | keyedOrdinal v == n} @-}
mkKeyed :: (Rel row) => Int -> Keyed row
mkKeyed n = Keyed n (Keys mempty)
