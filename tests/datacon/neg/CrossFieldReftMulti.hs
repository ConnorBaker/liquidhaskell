{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Illegal type specification" @-}

-- | The multi-component twin of @CrossFieldReft.hs@: field @b@'s bound names
-- its sibling @a@, an @{-# UNPACK #-}@ed two-field product.
--
-- 'RefType.mkProductTy''s multi-component branch RENAMES the field --
-- @a@ becomes @a##T##expand##1@, @a##T##expand##2@ -- and 'reftOnLast'
-- rebuilds only @a@'s OWN refinement over the components. @b@'s @p2Fst a@
-- is never touched, so its @a@ DANGLES: @Illegal type specification for `T`@
-- with @Unbound symbol a##T --- perhaps you meant: a##T##expand##1,
-- a##T##expand##2 ?@. The message's own suggestion is the fix.
--
-- Note the result refinement is already right --
-- @a VV == P2 a##T##expand##1 a##T##expand##2@ -- so the rebuild exists and
-- is applied to one of the two places that name the field. A GREEN means it
-- is applied to the sibling refinements too, and the module moves to @pos@
-- with 'useT' as its claim.
--
-- @-O0@ is SAFE, and 'useT' shows the dependent spec is enforced when no
-- expansion happens.
module CrossFieldReftMulti where

data P2 = P2 !Int !Int

{-@ measure p2Fst @-}
p2Fst :: P2 -> Int
p2Fst (P2 x _) = x

{-@ data T = T { a :: P2, b :: {v:Int | v == p2Fst a} } @-}
data T = T { a :: {-# UNPACK #-} !P2, b :: !Int }

mk :: Int -> Int -> T
mk x y = T (P2 x y) x

{-@ useT :: T -> {v:Int | v == 0} @-}
useT :: T -> Int
useT (T p n) = n - p2Fst p
