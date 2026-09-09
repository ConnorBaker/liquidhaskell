{-# OPTIONS_GHC -O1 #-}

-- | Two levels of unpacking under a nested @case@: @D@'s only field is an
-- @{-# UNPACK #-}@ed @Pair@ standing on TWO worker arguments, and @Pair@'s
-- first field @W@ wraps a @Set@ and resorts.
--
-- This was a NEGATIVE until the 'RepMap' commit, pinning the refusal
-- @has no selector in the logic@ for @Pair@'s resorted field. That selector
-- is kept now -- its equation is @Pair.sel1 (Pair y n) = W y@ -- so the
-- projection composes: @bx1 := W.sel1 (Pair.sel1 (D.sel1 d))@,
-- @bx2 := Pair.sel2 (D.sel1 d)@, and the Core body @Pair bx1 bx2@ becomes
-- @Pair (W.sel1 (Pair.sel1 X)) (Pair.sel2 X)@ with @X = D.sel1 d@. That is
-- the eta redex of @Pair@ over its LEAVES, and 'etaCollapse' -- generalised
-- from @C (sel_1 e) .. (sel_n e)@ to the full leaf projections -- collapses
-- it to @D.sel1 d@. Left standing it is well sorted and UNPROVABLE without
-- PLE, since the solver has no equations for @W.sel1@ applied to a @W@ it
-- never saw constructed: measured, 'useBox' is @Liquid Type Mismatch@ with
-- the collapse restricted to plain selectors and SAFE with it.
--
-- 'useBox' is the claim; @tests/datacon/neg/NestedCaseProjectionDeep.hs@
-- demands its negation.
module NestedCaseProjectionDeep where

import Data.Set (Set)

data W = W (Set Int)

data Pair = Pair !W !Int

data D = D {-# UNPACK #-} !Pair

data Box = Box D

{-@ measure boxPair @-}
boxPair :: Box -> Pair
boxPair (Box d) = case d of D q -> q

{-@ useBox :: x:Box -> {v:Pair | v == boxPair x} @-}
useBox :: Box -> Pair
useBox (Box (D q)) = q
