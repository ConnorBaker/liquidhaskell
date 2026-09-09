{-# OPTIONS_GHC -O1 #-}

-- | Control: a @{-@ invariant @-}@ on the TYPE plus a bound on an unpacked
-- field.
--
-- An invariant is stated at SOURCE sorts and attached to the type
-- constructor ('Constraint.Init.mkRTyConInv'), not to the data constructor,
-- so the worker/wrapper seam should not touch it. The field's bound goes
-- through 'mkProductTy''s @keepReft@ with equal sorts -- @Int@ and @Int#@ are
-- both @int@ -- which is the verbatim-copy branch. No module under
-- @tests/datacon@ combined the two before this one.
--
-- A red here would mean either the invariant is re-sorted against the worker
-- or the equal-sort copy fails.
module UnpackedFieldInvariant where

data T = T { tN :: !Int }

{-@ data T = T { tN :: {v:Int | 0 <= v} } @-}

{-@ invariant {v:T | 0 <= tN v} @-}

{-@ mk :: {n:Int | 0 <= n} -> T @-}
mk :: Int -> T
mk n = T n

{-@ useT :: T -> {v:Int | 0 <= v} @-}
useT :: T -> Int
useT (T n) = n
