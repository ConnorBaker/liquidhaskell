{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The negative companion of @tests/datacon/pos/CrossFieldReft.hs@: the
-- dependent bound @b == wOf a@ gives @n - wOf w == 0@ and nothing more, so a
-- claim of @1@ must fail. Without this the positive is discharged just as
-- well by a rewrite that rebuilt the sibling reference as @true@.
module CrossFieldReft where

data W = W !Int

{-@ measure wOf @-}
wOf :: W -> Int
wOf (W n) = n

{-@ data T = T { a :: W, b :: {v:Int | v == wOf a} } @-}
data T = T { a :: !W, b :: !Int }

{-@ useT :: T -> {v:Int | v == 1} @-}
useT :: T -> Int
useT (T w n) = n - wOf w
