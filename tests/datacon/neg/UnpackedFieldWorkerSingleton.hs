{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
-- | The GUARD for 'tests/datacon/pos/UnpackedFieldWorkerSingleton.hs', NOT its
-- attribution: before the fix this module also failed -- with the same
-- @Liquid Type Mismatch@, because nothing about the wrapper was provable in
-- either direction -- so it was already red and says nothing about the change.
--
-- What it pins is the direction that matters for SOUNDNESS. Identifying the
-- wrapper's singleton with the worker's can only make MORE things provable,
-- which is how an expected failure turns into a silent pass. @setPrio@ keeps
-- the scrutinee's own priority while claiming to install @p@, so the claim is
-- false exactly when they differ, and it must stay UNSAFE.
module UnpackedFieldWorkerSingleton where

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
setPrio d _ = Dep (depPrio d) (depNote d)
