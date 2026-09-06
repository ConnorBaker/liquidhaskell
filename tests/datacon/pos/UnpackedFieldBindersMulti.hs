{-# OPTIONS_GHC -O1 #-}

-- | The multi-component half of 'UnpackedFieldBinders', which that module no
-- longer reaches.
--
-- 'mkProductTy' has two branches. A SINGLE-component expansion keeps the
-- caller's binder; a MULTI-component one has to invent a name per component,
-- and naming them all @dummySymbol@ -- one fixed name, not a fresh one -- makes
-- the constructor's result refinement assert @sel_1 VV == sel_2 VV@.
--
-- @UnpackedFieldBinders@ was written for that branch and stopped reaching it:
-- it relies on a 3-field @Extent@ being expanded, and once expansion was
-- restricted to what @-funbox-small-strict-fields@ ACTUALLY unpacks, GHC's
-- refusal to unpack a 3-field product made the branch unreachable from there.
-- Measured: disarming the binder fix moves neither that module nor its
-- negative, and the only thing left reading on it was another commit's test.
--
-- Reaching the branch needs an explicit @{-# UNPACK #-}@ on a MULTI-field
-- product, which is the only thing that gives one source field several worker
-- arguments.
--
-- Three constraints on the shape, each of which cost an arm:
--
-- * The two components must have different SORTS, because where they agree the
--   collision is accepted in silence. @!Int@ beside @!Int@ and @!Int@ beside
--   @!Double@ are both quiet.
--
-- * Neither component may RESORT under unpacking, or its selector is dropped
--   and any measure over it is @Unbound symbol@ -- a real cost of the sort fix,
--   not of this one. That rules out a @Set@ behind a strict field, which was
--   the first shape tried here.
--
-- * @Tag@ is therefore LAZY. Left strict it unpacks to its @Bool@, which
--   resorts, and the module fails for the reason above rather than this one.
--
-- With @Tag@ lazy the worker is @Int# -> Tag -> Pair@, so @Boxed@ expands to
-- two components of sorts @int@ and @Tag@: different, and neither moved.
module UnpackedFieldBindersMulti where

data Tag = Tag Bool

data Pair = Pair !Int Tag

data Boxed = Boxed {-# UNPACK #-} !Pair

-- A measure over the unpacked field, so the module carries an obligation
-- rather than merely being accepted. Without it this reports
-- @SAFE (0 constraints checked)@ -- which a module with no refinements at all
-- also reports.
{-@ measure boxedPair @-}
boxedPair :: Boxed -> Pair
boxedPair (Boxed p) = p

{-@ mkBoxed :: p:Pair -> {v:Boxed | boxedPair v == p} @-}
mkBoxed :: Pair -> Boxed
mkBoxed = Boxed
