{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The negative companion of @tests/datacon/pos/CrossFieldReftMulti.hs@:
-- the dependent bound @b == p2Fst a@ gives @n - p2Fst p == 0@ and nothing
-- more, so a claim of @1@ must fail.
module CrossFieldReftMulti where

data P2 = P2 !Int !Int

{-@ measure p2Fst @-}
p2Fst :: P2 -> Int
p2Fst (P2 x _) = x

{-@ data T = T { a :: P2, b :: {v:Int | v == p2Fst a} } @-}
data T = T { a :: {-# UNPACK #-} !P2, b :: !Int }

{-@ useT :: T -> {v:Int | v == 1} @-}
useT :: T -> Int
useT (T p n) = n - p2Fst p
