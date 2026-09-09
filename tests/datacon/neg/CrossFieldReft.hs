{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Illegal type specification" @-}

-- | A DEPENDENT record refinement: field @b@'s bound names its SIBLING @a@,
-- and @a@ is a strict single-field product that
-- @-funbox-small-strict-fields@ unboxes to the @Int@ inside it.
--
-- 'RefType.mkProductTy''s single-component branch KEEPS the binder @a@ -- the
-- 19414eea fix -- but at the COMPONENT's sort: @a : int@ now, where the user
-- wrote @a : W@. 'keepReft' rewrites only @a@'s OWN refinement, which is
-- trivial here. @b@'s refinement still says @v == wOf a@, so
-- @wOf : W -> int@ is applied to an @int@ and the declaration is rejected:
-- @Illegal type specification for `T`@ with
-- @Cannot unify W with int in expression: wOf a##T@. The selectors 'a' and
-- 'b' are rejected with it, 'a' as @Unbound symbol@ because
-- 'Bare.resortedFields' correctly dropped it.
--
-- Every shipped refinement under @tests/datacon@ mentions only its own field.
-- A constructor's spec is a DEPENDENT function type and this is the first arm
-- to lean on that. A GREEN means the sibling reference is rebuilt as well --
-- @a@ replaced by @W a@ in every later binder's refinement, the same
-- substitution 'rebuiltOverComponent' applies to the field's own -- and the
-- module moves to @pos@ with 'useT' as its claim.
--
-- @-O0@ is SAFE, and it also shows the dependent spec is ENFORCED there:
-- 'useT' needs @b == wOf a@.
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
