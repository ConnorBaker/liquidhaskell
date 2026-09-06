{-# OPTIONS_GHC -O1 #-}

-- | 'Bare.resortedFields' must answer per EXPANSION, because a constructor can
-- carry a RESORTED field and an EXPANDING one at the same time.
--
-- A field selector is declared at the field's SOURCE type while the
-- constructor's spec is bound at the WORKER's argument types, and the result
-- refinement states @sel_i VV == b_i@ across the two. 'resortedFields' is the
-- one authority on which fields have moved, and 'makeMeasureSelectors' drops
-- their selectors so no such equation is ever emitted.
--
-- It used to compare the source and worker lists head-to-head and answer
-- 'False' throughout whenever their value arities disagreed. That reads as the
-- conservative choice and is not one: 'False' KEEPS the selector, so the guard
-- disarms itself on exactly the shape below and the declaration is rejected
-- with @Illegal type specification for `T`@ and @Cannot unify IORef with
-- (MutVar# ...)@, naming @Just constructor@ and no field -- the very error
-- dropping the selector exists to prevent.
--
-- Both fields are load-bearing and each is a free control on its own:
--
--   * @!(IORef Int)@ alone (drop the @UNPACK@) is 'UnpackedFieldSorts'' shape
--     and was always fine -- one argument either way, so the arities agree.
--   * @{-\# UNPACK \#-} !Extent@ alone (make the first field @!Int@) is fine
--     too: it expands, but no field's sort moves. That is
--     'UnpackedFieldExpandedOnly', and it is a CONTROL rather than a
--     remark: without it a fix that refused every expanding constructor
--     would make this module green and look correct.
--
-- @{-\# UNPACK \#-}@ is required and a bare @!Extent@ does NOT do it:
-- @-funbox-small-strict-fields@ unpacks only single-WORD strict fields, so a
-- two-field 'Extent' is left alone and the arities never disagree. That is why
-- the shape went unseen behind nine other @-O1@ fixes.
--
-- 'mkT' is what makes this module test the fix rather than the symptom. A
-- measure on its own raises no obligation and reports
-- @SAFE (0 constraints checked)@, which is nothing proved.
module UnpackedFieldExpandedSorts where

import Data.IORef (IORef)

data Extent = Extent !Int !Int

data T = T !(IORef Int) {-# UNPACK #-} !Extent

{-@ measure widthOf @-}
widthOf :: T -> Int
widthOf (T _ (Extent w _)) = w

{-@ mkT :: r:(IORef Int) -> w:Int -> h:Int -> {v:T | widthOf v == w} @-}
mkT :: IORef Int -> Int -> Int -> T
mkT r w h = T r (Extent w h)
