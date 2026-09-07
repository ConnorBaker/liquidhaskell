{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=has no selector in the logic" @-}

-- | The 'unpackedFieldSubst' twin of
-- @tests/datacon/neg/NestedCaseProjectionSort.hs@: a lifted equation whose OWN
-- top-level alternative -- not a nested @case@ -- projects through a field that
-- has no selector.
--
-- That module's header named this shape as the one it deliberately avoids, and
-- said the path "has the same gap and is left for its own commit". Make @A2@'s
-- field STRICT and the equation is rewritten by 'unpackedFieldSubst', which
-- carried no refusal at all: the failure was
-- @Unbound symbol A2.C##lqdc##$select##C##1@ reported at the DATA DECLARATION
-- @data A2 = A2 !C@, naming neither the measure that wanted the selector nor
-- the field that lost it.
--
-- This is also the module that refutes the cheap version of 'droppedSelectors'.
-- Recording a resorted field WITHOUT descending through it catches every deeper
-- shape and misses this one: @A2@'s own field resorts, so the table holds
-- @A2@'s selector -- which the composition never names, because it starts at
-- the source argument binder -- and not @C@'s, which it does.
--
-- @--expect-error-containing@ rather than @--expect-any-error@: this module
-- failed before the change too, so the weaker form is discharged by the very
-- defect the message exists to replace.
module UnpackedFieldSubstSort where

import Data.Set (Set)

data W = W (Set Int)

data C = C !W

data A2 = A2 !C

{-@ measure a2C @-}
a2C :: A2 -> C
a2C (A2 c) = c
