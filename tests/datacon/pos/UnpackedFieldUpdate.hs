{-# OPTIONS_GHC -O1 #-}

-- | A lifted SELECTOR measure must describe the constructor's WRAPPER as well
-- as its worker, or every record update becomes unprovable from @-O1@ up.
--
-- @makeDataConType@ splits a constructor's measure equations in two. One with
-- all its argument types available comes from a user definition and was given
-- to both the worker and the wrapper; one with types MISSING comes from a
-- selector or checker measure -- the equations a @{-\@ data \@-}@ block
-- generates -- and was given to the worker ALONE, on a comment's assumption
-- that a selector "describes the worker data constructor".
--
-- That assumption holds exactly while the two take the same arguments. Below
-- @-O1@ there is no wrapper at all. From @-O1@ up
-- @-funbox-small-strict-fields@ rewrites 'sUnpacked' to an @Int#@, GHC builds
-- a wrapper to do the boxing, and a record update -- @s { sFlag = False }@,
-- which compiles to a CONSTRUCTION -- goes through that wrapper. The inferred
-- type then quotes @$WS ...@ while every @sFlag (S ...) == x@ fact in scope is
-- about the worker @S@, so the refinement on 'clearFlag' is not provable and
-- the error names the update site rather than the data type.
--
-- A selector equation is written over the constructor's SOURCE fields, which
-- is exactly the wrapper's argument list, so giving it to the wrapper needs no
-- reconstruction -- unlike the WORKER direction, which does, and which
-- @tests/datacon/pos/UnpackedFieldRebuild.hs@ covers.
--
-- Measured five ways before the fix, varying only the shape: with the @!Int@
-- field present this module is @SAFE (1)@ at @-O0@ and @UNSAFE (1)@ at @-O1@
-- and @-O2@; drop that field, or make it lazy, and it is @SAFE (1)@ at every
-- level. So UNPACKING is the variable, not @Int@ and not strictness, and
-- @-O0@ is a free control on both sides of the fix. Moving the @!Int@ field
-- last does not help, and refining the UNPACKED field itself fails
-- identically, so it is not about which field is named.
module UnpackedFieldUpdate where

{-@ data S = S
      { sUnpacked :: Int
      , sFlag :: Bool
      , sOther :: Bool
      } @-}
data S = S
  { sUnpacked :: !Int
  , sFlag :: !Bool
  , sOther :: !Bool
  }

-- The update site: a construction through the wrapper, with the postcondition
-- stated on the field the update writes.
{-@ clearFlag :: s:S -> {v : S | not (sFlag v)} @-}
clearFlag :: S -> S
clearFlag s = s {sFlag = False}

-- The same fact about the UNPACKED field, so the equation is exercised on both
-- sides of the expansion rather than only on a field the expansion skipped.
{-@ setUnpacked :: s:S -> {v : S | sUnpacked v == 1} @-}
setUnpacked :: S -> S
setUnpacked s = s {sUnpacked = 1}

-- A field the update does not touch must still be readable through the
-- wrapper, which is the half a per-field equation could get wrong.
{-@ preservesOther :: s:S -> {v : S | sOther v == sOther s} @-}
preservesOther :: S -> S
preservesOther s = s {sFlag = False}
