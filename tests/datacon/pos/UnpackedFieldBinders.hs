{-# OPTIONS_GHC -O1 #-}

-- | A data constructor's binders must stay pairwise DISTINCT once GHC unpacks
-- one of its strict fields.
--
-- @expandProductType@ rewrites a constructor's argument list when the worker's
-- type stops matching the spec's, which is what @-O1@ causes here: the small
-- strict @Int@ field is unpacked to @Int#@. Every expanded component used to be
-- named @dummySymbol@ -- ONE fixed name, not a fresh one -- so two fields ended
-- up bound to the same symbol. The result refinement of a constructor names its
-- binders (@select_i VV == b_i@), so that silently asserted the two fields were
-- equal, and where their sorts could not unify LiquidHaskell rejected the
-- declaration outright.
--
-- @-O1@ IS THE POINT OF THIS MODULE. At @-O0@ nothing is unpacked, the guard in
-- @expandProductType@ short-circuits, and the bug is unreachable -- this module
-- was @SAFE@ at @-O0@ and @Illegal type specification for `Section`@ at @-O1@
-- before the fix.
--
-- The SECOND field has to be an expandable product of its own -- a
-- single-constructor type with several fields, which is @Data.Text.Text@'s
-- shape and is why that type surfaced it first. A list, a @Maybe@ or a function
-- there does not reproduce.
--
-- 'mkSection' is the attribution half: it is provable only if the surviving
-- binder still names the field it always named. A fix that made the components
-- distinct by giving them all FRESH names would clear the error above and break
-- this, so the module tests the fix rather than merely the symptom.
module UnpackedFieldBinders where

data Extent = Extent Int Int Int

data Section = Section
  { sectionOrdinal :: !Int
  , sectionExtent :: Extent
  }

{-@ measure sectionOrdinal @-}

{-@ mkSection :: n:Int -> {v:Section | sectionOrdinal v == n} @-}
mkSection :: Int -> Section
mkSection n = Section n (Extent 0 0 0)
