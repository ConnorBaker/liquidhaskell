{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=has no selector in the logic" @-}

-- | The refusal was decided at ONE constructor while the projection composition
-- descends TRANSITIVELY, and this is the shape that falls through the gap.
--
-- @D@'s only field is an @{-# UNPACK #-}@ed @Pair@, which stands on TWO worker
-- arguments -- so 'Bare.resortedFields' answers @moved _ _ = False@ for it and
-- @D@ keeps a perfectly good selector. 'fieldRepProjs' then descends INTO
-- @Pair@, whose first field @W@ wraps a @Set@ and resorts, so
-- @Pair##lqdc##$select##Pair##1@ was never declared. Asking only about @D@ lets
-- the composition name it anyway.
--
-- The gap matters because copying the guard was the recorded plan: this
-- repository's own notes proposed giving 'unpackedFieldSubst' "the guard
-- 'altToLg' already carries", and that guard is the one this module walks past.
--
-- Before the change: @Unbound symbol@ at @data Box = Box D@, naming neither
-- field nor reason -- hence @--expect-error-containing@ and not
-- @--expect-any-error@, which that failure discharges too.
--
-- @Box@'s field is LAZY, for the reason @NestedCaseProjection.hs@ records:
-- unpacked, the outer equation goes through 'unpackedFieldSubst' instead, and
-- that site is covered one level shallower by
-- @tests/datacon/neg/UnpackedFieldSubstSort.hs@. The strict two-level twin of
-- this module WAS written and is deliberately NOT shipped: it is red under
-- every mutant that reddens @UnpackedFieldSubstSort.hs@ and green under every
-- mutant that leaves it green, so it detects nothing that module does not.
module NestedCaseProjectionDeep where

import Data.Set (Set)

data W = W (Set Int)

data Pair = Pair !W !Int

data D = D {-# UNPACK #-} !Pair

data Box = Box D

{-@ measure boxPair @-}
boxPair :: Box -> Pair
boxPair (Box d) = case d of D q -> q
