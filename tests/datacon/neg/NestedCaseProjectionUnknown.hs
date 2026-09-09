{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=has no selector in the logic" @-}

-- | The shape that STILL has no selector after the 'RepMap' commit, pinned
-- where @NestedCaseProjectionSort.hs@ used to pin it: a strict @IORef@ field.
-- @-funbox-small-strict-fields@ unpacks it through the newtype @IORef@ and
-- the product @STRef@ to a @MutVar#@, so @C@'s field resorts, and its
-- selector's equation would be @C.sel1 (C mv) = IORef (STRef mv)@ --
-- naming two constructors the logic has no datatype for. So the selector is
-- dropped ('fieldSelectorDropped'), 'altToLg' cannot project through it, and
-- the equation is refused at the measure that asked, naming the field --
-- rather than lifted around an undeclared symbol and rejected at the DATA
-- DECLARATION with @Unbound symbol@, which is what @--expect-any-error@
-- would also have accepted.
module NestedCaseProjectionUnknown where

import Data.IORef (IORef)

data C = C !(IORef Int)

data A2 = A2 C

{-@ measure a2R @-}
a2R :: A2 -> IORef Int
a2R (A2 c) = case c of C r -> r
