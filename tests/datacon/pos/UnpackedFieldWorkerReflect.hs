{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
-- | The arm that decides WHEN the worker rewrite applies, and it is the same
-- module as 'tests/datacon/pos/UnpackedFieldWorkerSingleton.hs' plus
-- @--reflection@.
--
-- With @--reflection@ (or @--adt@) LiquidHaskell DECLARES the datatype to the
-- SMT solver -- @Constraint.ToFixpoint@'s @makeDecls = adtFlag cfg@ -- and it
-- declares it from the SOURCE fields. The logic's constructor symbol is then
-- bound at the source sorts, the @-O1@ worker/wrapper seam does not arise, and
-- rewriting a construction onto the worker's representation arguments is
-- exactly wrong: it emits @Dep p (notesSet n)@ against a
-- @Dep : func([Prio; Notes; Dep])@.
--
-- The failure is loud but unattributable -- @Cannot unify Notes with
-- (Array_t Text bool)@ raised from @evalCandsLoop@ at @Fixpoint.Types.dummyLoc@,
-- naming no binder and no module -- which is why this arm exists rather than a
-- comment.
module UnpackedFieldWorkerReflect where

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

{-@ reflect mkDep @-}
mkDep :: Prio -> Notes -> Dep
mkDep p n = Dep p n

{-@ setPrio :: d:Dep -> p:Prio -> {v:Dep | v == mkDep p (depNote d)} @-}
setPrio :: Dep -> Prio -> Dep
setPrio d p = Dep p (depNote d)
