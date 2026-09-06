{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--ple" @-}
-- | The CONSTRAINT-GENERATION half of the seam
-- 'tests/datacon/pos/UnpackedFieldWorkerApp.hs' covers on the LIFTING half.
--
-- @setPrio@ is not reflected, so its body's type is INFERRED, and for a
-- construction from @-O1@ up the head GHC compiles is the wrapper @$WDep@.
-- @mkDep@ IS reflected, so its body is lifted onto the worker @Dep@. The two
-- halves have to meet: with the singleton stated over @$WDep@ and the
-- reflected body over @Dep@, nothing relates them and the postcondition is
-- undischargeable -- silently, since both terms are well sorted.
--
-- At @-O0@ there is no wrapper and this module is SAFE with no fix at all, so
-- 'tests/datacon/pos/UnpackedFieldWorkerSingleton0.hs' is a free control.
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
setPrio d p = Dep p (depNote d)
