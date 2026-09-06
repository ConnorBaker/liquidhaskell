-- | A reflected body that CONSTRUCTS must name the same logic symbol as every
-- fact in scope about what it constructed.
--
-- The logic has exactly ONE symbol per data constructor -- @F.Symbolic DataCon@
-- is @F.symbol . dataConWorkId@ -- and Haskell has TWO argument lists. Below
-- @-O1@ they coincide and GHC builds no wrapper, so lifting a construction by
-- @symbol@ happens to name the worker. From @-O1@ up
-- @-funbox-small-strict-fields@ unpacks @Notes@ into @Dep@, GHC compiles the
-- construction as a call to @$WDep@, and @coreToLg@'s @C.Var@ case lifted that
-- to a SECOND, unrelated uninterpreted constant at the SOURCE field sorts:
--
-- > constant M.$WDep : func(0, [M.Prio; M.Notes;          M.Dep])
-- > constant M.Dep   : func(0, [M.Prio; (Set_Set M.Text); M.Dep])
--
-- Nothing relates them, so @depCombine a a@ unfolded to @$WDep ..@ while the
-- environment knew only @a == Dep ?p bx@ and @depNote a == Notes bx@. This is
-- the CONSTRUCTION direction of the seam @unpackedFieldSubst@ handles for
-- projection, and it is quiet in the dangerous direction: the term is well
-- sorted, so there is no error and no message -- the obligation is merely
-- undischargeable, far from the constructor, and only above @-O0@.
--
-- @-O0@ is a free control: the three levels give an IDENTICAL constraint count,
-- so the obligations were always raised and only their discharge moved.
--
-- The two idempotence lemmas are the carriers rather than the subject. Their
-- proofs are trivial; what the module measures is whether @combineIdem@ can
-- get from them to a statement about @depCombine@, which it can only do if the
-- reflected body and the constructor facts speak about the same symbol.
{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--ple" @-}
module UnpackedFieldWorkerApp where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)

{-@ data Notes = Notes (notesSet :: Set Text) @-}
data Notes = Notes !(Set Text)

{-@ reflect notesUnion @-}
notesUnion :: Notes -> Notes -> Notes
notesUnion (Notes l) (Notes r) = Notes (Set.union l r)

{-@ notesIdem :: a:Notes -> {u:() | notesUnion a a == a} @-}
notesIdem :: Notes -> ()
notesIdem (Notes _) = ()

data Prio = Lo | Hi

{-@ reflect stronger @-}
stronger :: Prio -> Prio -> Prio
stronger Hi _ = Hi
stronger Lo b = b

{-@ prioIdem :: a:Prio -> {u:() | stronger a a == a} @-}
prioIdem :: Prio -> ()
prioIdem Hi = ()
prioIdem Lo = ()

-- @Prio@ is deliberately beside @Notes@: it does not resort, so it holds the
-- rest of the constructor fixed while the note field is the only one whose
-- source and representation types differ.
data Dep = Dep !Prio !Notes

depPrio :: Dep -> Prio
depPrio (Dep p _) = p

depNote :: Dep -> Notes
depNote (Dep _ n) = n

{-@ measure depPrio @-}
{-@ measure depNote @-}

{-@ reflect depCombine @-}
depCombine :: Dep -> Dep -> Dep
depCombine a b =
  Dep (stronger (depPrio a) (depPrio b)) (notesUnion (depNote a) (depNote b))

{-@ combineIdem :: a:Dep -> {u:() | depCombine a a == a} @-}
combineIdem :: Dep -> ()
combineIdem a@(Dep _ _) = case prioIdem (depPrio a) of () -> notesIdem (depNote a)
