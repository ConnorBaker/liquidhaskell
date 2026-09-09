{-# OPTIONS_GHC -O1 #-}

-- | A DEPENDENT record refinement: field @b@'s bound names its SIBLING @a@,
-- and @a@ is a strict single-field product that
-- @-funbox-small-strict-fields@ unboxes to the @Int@ inside it.
--
-- This was a NEGATIVE until the 'RepMap' commit, pinning
-- @Illegal type specification@. Two things were wrong. The expansion rewrote
-- only @a@'s OWN refinement over its component and left @b@'s @v == wOf a@
-- naming an @a@ that was now an @int@; 'RefType.expandOver' threads the
-- substitution @a := W a@ through every later field's refinement and the
-- result. And the selector @a@ was DROPPED because its sort moved, so the
-- record selector's signature @a :: z:T -> {v | v == a z}@ named an unbound
-- symbol; a selector is now dropped only when its equation
-- @a (T y m) = W y@ cannot be stated ('fieldSelectorDropped'), and @W@ is a
-- constructor the logic knows.
--
-- 'useT' is the claim, and it is the dependent one: it needs @b == wOf a@
-- from the declaration. @tests/datacon/neg/CrossFieldReft.hs@ demands
-- @v == 1@ of the same body.
--
-- @-O0@ is SAFE: no unboxing, no expansion.
module CrossFieldReft where

data W = W !Int

{-@ measure wOf @-}
wOf :: W -> Int
wOf (W n) = n

{-@ data T = T { a :: W, b :: {v:Int | v == wOf a} } @-}
data T = T { a :: !W, b :: !Int }

mk :: Int -> T
mk n = T (W n) n

{-@ useT :: T -> {v:Int | v == 0} @-}
useT :: T -> Int
useT (T w n) = n - wOf w
