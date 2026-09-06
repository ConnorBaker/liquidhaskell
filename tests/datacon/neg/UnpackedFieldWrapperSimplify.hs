-- | The guard for 'tests/datacon/pos/UnpackedFieldWrapperSimplify.hs', and NOT
-- its attribution -- before the fix this module also failed, with the
-- @evalCandsLoop@ elaboration error rather than a type mismatch, so
-- @--expect-any-error@ would have been discharged by the very defect the
-- positive exists to catch.
--
-- What it pins is that dropping the WRAPPER's duplicate rewrite did not drop
-- the fact: the worker's own entry still supplies the equation, so a FALSE
-- claim about the measure is still caught rather than passing vacuously.
{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
module UnpackedFieldWrapperSimplify where

import Data.Set (Set)
import Data.Text (Text)

{-@ data Notes = Notes (notesSet :: Set Text) @-}
data Notes = Notes !(Set Text)

data Prio = Lo | Hi

data Dep = Dep !Prio !Notes

depPrio :: Dep -> Prio
depPrio (Dep p _) = p

depNote :: Dep -> Notes
depNote (Dep _ n) = n

{-@ measure depPrio @-}
{-@ measure depNote @-}

{-@ prioOfDep :: p:Prio -> s:Set Text -> {u:() | depPrio (Dep p s) == Hi} @-}
prioOfDep :: Prio -> Set Text -> ()
prioOfDep _ _ = ()
