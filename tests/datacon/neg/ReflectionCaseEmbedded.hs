{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--expect-error-containing=Cannot unify" @-}

-- | Under @--reflection@ the datatype is DECLARED to the SMT solver, from the
-- SOURCE fields ('Bare.DataType.makeDataCtor' over @dcpTyArgs@, gated by
-- @makeDecls = adtFlag cfg@) -- so @Dep : func([int; Notes; Dep])@. A case
-- alternative's binders are the REPRESENTATION arguments, and
-- 'Constraint.Generate.caseEnv' emits @dataConReft@ over them:
-- @v == Dep bx0 bx1@ with @bx1 : Set_Set int@, the unpacked component of the
-- @Notes@ field. 'workerApp' declines under @adtFlag@, so the lifting side
-- does not reconcile the two shapes either.
--
-- This is the regime split the series left in place: @adtFlag@ selects
-- source-shaped declarations at ONE site while every other site is
-- rep-shaped. @tests/datacon/pos/UnpackedFieldWorkerReflect.hs@ has this
-- exact @Dep@/@Notes@ shape, cases on @Dep@, and is SAFE -- a case ALONE does
-- not fire. What fires it is a postcondition that can only be discharged
-- through the alternative's singleton: @v == notesSet (depNote d)@.
--
-- The failure is a liquid-fixpoint sort error with no verdict:
-- @Cannot unify Notes with (Array_t int bool) in expression: Dep bx0 bx1@,
-- naming the constructor and neither the module's flag nor the field. A GREEN
-- means the two regimes were unified -- @adtFlag@ selecting one shape for
-- 'makeDataCtor', 'caseEnv' and 'workerApp' together -- and the module moves
-- to @pos@ with 'keys' as its claim.
--
-- @-O0@ is SAFE: nothing is unpacked, so the case binder is @Notes@-sorted.
module ReflectionCaseEmbedded where

import Data.Set (Set)

{-@ data Notes = Notes (notesSet :: Set Int) @-}
data Notes = Notes !(Set Int)

data Dep = Dep !Int !Notes

depNote :: Dep -> Notes
depNote (Dep _ n) = n

{-@ measure depNote @-}

{-@ keys :: d:Dep -> {v:Set Int | v == notesSet (depNote d)} @-}
keys :: Dep -> Set Int
keys (Dep _ (Notes s)) = s
