{-# OPTIONS_GHC -O1 #-}

-- | The multi-component twin of @CrossFieldReft.hs@: field @b@'s bound names
-- its sibling @a@, an @{-# UNPACK #-}@ed two-field product.
--
-- This was a NEGATIVE until the 'RepMap' commit, pinning
-- @Illegal type specification@ with @Unbound symbol a##T --- perhaps you
-- meant: a##T##expand##1, a##T##expand##2@: the multi-component expansion
-- renamed the field and rebuilt only its OWN refinement over the components,
-- so @b@'s @p2Fst a@ dangled. 'RefType.expandOver' now threads
-- @a := P2 a##expand##1 a##expand##2@ through every later binder's
-- refinement, which is the message's own suggestion.
--
-- 'useT' is the claim. @tests/datacon/neg/CrossFieldReftMulti.hs@ demands
-- @v == 1@ of the same body.
--
-- @-O0@ is SAFE: no expansion happens.
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
