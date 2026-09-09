{-# OPTIONS_GHC -O1 #-}
-- A refinement WRITTEN on a strict field whose type the logic has no datatype
-- for, and whose sort GHC's unpacking moves: @IORef Int@ is a newtype over
-- @STRef@ over @MutVar#@, and -funbox-small-strict-fields makes the worker
-- take the @MutVar#@. The field cannot be REBUILT -- @IORef (STRef v)@ names
-- two constructors the logic does not have -- so its one worker argument
-- stands in for it and the refinement is copied verbatim onto the leaf. For
-- the field's OWN refinement that is what lh/integration (41c6c09b4) did:
-- this module is SAFE (1) there, and SAFE (1) here. (A SIBLING reference to
-- such a field is where the two differ -- @UnpackedFieldReftUnknownDep.hs@.)
-- The first cut of the RepMap commit refused it instead,
-- naming the constructor; the refusal is kept for the shape that has no other
-- reading, a multi-argument product the logic does not know
-- (@neg/UnpackedFieldReftUnknownProduct.hs@).
--
-- The verbatim copy is not a licence: @{v:IORef Int | false}@ on this field
-- is UNSAFE at 'mk' on both libraries (reviewer's probe, 2026-09-09), and any
-- comparison of @v@ with an @IORef@-sorted term is ill-sorted once @v@ is the
-- @MutVar#@, so only what holds of the leaf survives.
module UnpackedFieldReftUnknown where

import Data.IORef

data A = A !(IORef Int) !Int

{-@ data A = A (aRef :: {v:IORef Int | v == v}) (aN :: Int) @-}

{-@ mk :: r:IORef Int -> n:Int -> {v:A | aN v == n} @-}
mk :: IORef Int -> Int -> A
mk = A
