-- | A lifted measure equation must be stated over the argument list the LOGIC
-- uses for the constructor, which is the WORKER's.
--
-- @Notes@ is a single-constructor strict wrapper, so from @-O1@ up
-- @-funbox-small-strict-fields@ unpacks it into @Dep@ and the worker takes
-- @Set Text@ where the wrapper takes @Notes@. The logic has only ONE symbol for
-- @Dep@ -- @F.Symbolic DataCon@ is @F.symbol . dataConWorkId@ -- and
-- @mkProductTy@ binds it at the worker's types.
--
-- @makeSimplify@ was handed the WRAPPER's @(Var, SpecType)@ as well as the
-- worker's, and re-keyed its rewrites onto the worker symbol while leaving the
-- binders at the wrapper's SOURCE sorts. PLE then fired the rule at the
-- worker's expanded sorts and the body came with the wrong sort attached:
--
-- > elaborate evalToSMT:evalCandsLoop failed on:
-- >   depNote (Dep (ds : Prio) (bx : (Array_t Text bool))) == bx
-- >   Cannot unify Notes with (Array_t Text bool)
--
-- reported at @dummyLoc@, naming no binder and no module.
--
-- @--ple@ is load-bearing: without it the rule is never fired and the module is
-- merely @UNSAFE@. In production this candidate is reached through a reflected
-- combine over the two selectors rather than by naming the constructor here.
{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--ple" @-}
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

-- Both halves matter. The note half is where the sorts disagree; the priority
-- half does not resort, and holding it fixed is what shows the rule set was not
-- simply dropped wholesale when the wrapper's copy stopped being emitted.
{-@ noteOfDep :: p:Prio -> s:Set Text -> {u:() | depNote (Dep p s) == Notes s} @-}
noteOfDep :: Prio -> Set Text -> ()
noteOfDep _ _ = ()

{-@ prioOfDep :: p:Prio -> s:Set Text -> {u:() | depPrio (Dep p s) == p} @-}
prioOfDep :: Prio -> Set Text -> ()
prioOfDep _ _ = ()
