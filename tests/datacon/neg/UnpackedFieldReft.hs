{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The negative half of @tests/datacon/pos/UnpackedFieldReft.hs@: carrying the
-- field's refinement across the unpacking must not carry MORE than was
-- written. @v <= flim@ is stated; @v <= flim / 2@ is not, and must still be
-- rejected at @-O1@.
--
-- Without this arm the positive is discharged by anything that makes the field
-- refinement strong enough, including a bug that put the wrong refinement
-- there -- the fix substitutes a reft onto a type it did not come from, so
-- "some refinement arrived" and "the right refinement arrived" are genuinely
-- different outcomes.
module UnpackedFieldReft where

{-@ inline flim @-}
flim :: Int
flim = 1024

{-@ data F = F [Int] {v : Int | v <= flim} @-}
data F = F ![Int] !Int

{-@ needHalf :: {v : Int | v <= 512} -> Int @-}
needHalf :: Int -> Int
needHalf x = x

useF :: F -> Int
useF (F _ n) = needHalf n
