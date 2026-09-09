{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The negative companion of @tests/datacon/pos/NestedCaseProjectionDeep.hs@:
-- the collapsed equation @boxPair (Box d) = D.sel1 d@ is an EQUALITY, so its
-- negation must fail. An 'etaCollapse' that collapsed to the wrong base --
-- any subterm of the first projection other than the one all of them
-- project -- would still be well sorted.
module NestedCaseProjectionDeep where

import Data.Set (Set)

data W = W (Set Int)

data Pair = Pair !W !Int

data D = D {-# UNPACK #-} !Pair

data Box = Box D

{-@ measure boxPair @-}
boxPair :: Box -> Pair
boxPair (Box d) = case d of D q -> q

{-@ bad :: x:Box -> {v:Pair | v /= boxPair x} @-}
bad :: Box -> Pair
bad (Box (D q)) = q
