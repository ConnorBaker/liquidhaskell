{-# OPTIONS_GHC -O1 #-}

-- | A data constructor's arguments must be bound at the sorts its own field
-- SELECTORS are declared at.
--
-- The two come from different places and only agree below @-O1@. A selector is
-- declared at the field's SOURCE type ('bkDataCon' reads
-- @Ghc.dataConFullSig@), while the constructor's spec is bound at the WORKER's
-- argument types, because that is what the "Specified type does not refine
-- Haskell type" check compares against. The constructor's result refinement
-- then states @sel_i VV == b_i@ between the two.
--
-- From @-O1@ up, @-funbox-small-strict-fields@ rewrites a strict field to its
-- representation. Two cases, and the whole fix turns on telling them apart:
--
--   * @!Int@ becomes @Int#@. HARMLESS -- both embed to the SMT sort @int@, so
--     the equation is well-sorted and 'mkT' below is provable.
--   * a strict single-field product such as @IORef a@ becomes the @MutVar#@
--     inside it. NOT harmless: the sorts differ, and before the fix the whole
--     declaration was rejected with @Illegal type specification for `T`@ and
--     @Cannot unify GHC.Internal.IORef.IORef with
--     (GHC.Internal.Prim.MutVar# ...)@, naming the TYPE and no field.
--
-- So the criterion is the SORT, not the type. 'mkT' is what makes this module
-- test the fix rather than the symptom: a fix that compared TYPES would drop
-- @tb@'s selector as well -- @Int@ and @Int#@ are different types -- clear the
-- error, and leave @tb v == n@ unprovable. Both fields must be present for the
-- module to mean anything, and @-O1@ is required.
--
-- THE COST, stated because it is a real behaviour difference between @-O0@ and
-- @-O1@ rather than a pure repair: @ta@ has no selector at @-O1@, so it cannot
-- be named in the logic and a @{-\@ measure ta \@-}@ is rejected with
-- @Unbound symbol GHC.Internal.IORef.IORef@. That is the sound direction --
-- the field is simply anonymous, exactly as a function-typed field already is,
-- and nothing that was unprovable becomes provable -- but it is a difference.
module UnpackedFieldSorts where

import Data.IORef (IORef, newIORef)

data T = T
  { ta :: !(IORef Int)
  , tb :: !Int
  }

{-@ measure tb @-}

{-@ mkT :: r:(IORef Int) -> n:Int -> {v:T | tb v == n} @-}
mkT :: IORef Int -> Int -> T
mkT = T

-- The same claim through a constructor APPLICATION rather than an eta-reduced
-- reference to the wrapper, so the worker's own spec is exercised.
{-@ freshT :: n:Int -> IO {v:T | tb v == n} @-}
freshT :: Int -> IO T
freshT n = do
  r <- newIORef 0
  pure (T r n)
