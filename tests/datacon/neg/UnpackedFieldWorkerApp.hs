-- | The guard for 'tests/datacon/pos/UnpackedFieldWorkerApp.hs', and NOT its
-- attribution: this module is @UNSAFE@ before the fix as well as after, because
-- before it nothing about a construction was provable in either direction. It
-- would pass while proving nothing, which is why the positive is the arm that
-- attributes and this one only holds the line.
--
-- The line it holds is the one a fix of this shape can cross. Rewriting a
-- wrapper application onto the worker symbol IDENTIFIES two terms that were
-- distinct, so it can only ever make MORE things provable -- exactly the
-- direction in which an expected failure turns into a silent pass. @depCombine@
-- unions the two note sets, so @depCombine a b == a@ is false as soon as @b@
-- carries a note @a@ does not, and it must stay caught.
--
-- @--expect-error-containing@ rather than @--expect-any-error@: the weaker form
-- is discharged by the first failing binder whatever went wrong, including the
-- elaboration and sort errors this series of fixes exists to remove.
{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
module UnpackedFieldWorkerApp where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)

{-@ data Notes = Notes (notesSet :: Set Text) @-}
data Notes = Notes !(Set Text)

{-@ reflect notesUnion @-}
notesUnion :: Notes -> Notes -> Notes
notesUnion (Notes l) (Notes r) = Notes (Set.union l r)

data Prio = Lo | Hi

{-@ reflect stronger @-}
stronger :: Prio -> Prio -> Prio
stronger Hi _ = Hi
stronger Lo b = b

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

{-@ combineBad :: a:Dep -> b:Dep -> {u:() | depCombine a b == a} @-}
combineBad :: Dep -> Dep -> ()
combineBad a@(Dep _ _) b@(Dep _ _) = const () (a, b)
