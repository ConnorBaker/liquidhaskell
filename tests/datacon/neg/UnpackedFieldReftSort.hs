{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The companion to @tests/datacon/pos/UnpackedFieldReftSort.hs@, and the arm
-- that makes its @SAFE@ mean something.
--
-- Same shape, same unpacked field whose sort changes, but the consumer demands
-- @wOf v <= 3@ where the declaration gives @wOf v <= 10@. The rebuilt
-- refinement must carry the bound that was WRITTEN, so this must fail.
--
-- Without this arm the positive is discharged equally well by a rebuild that
-- asserts @true@ -- and by the behaviour that preceded it, which dropped the
-- refinement entirely and would leave both modules failing at the consumer.
-- A positive alone cannot tell a correct transfer from a vacuous one.
module UnpackedFieldReftSort where

data W = W Int

{-@ measure wOf @-}
wOf :: W -> Int
wOf (W n) = n

{-@ data G = G [Int] {v : W | wOf v <= 10} @-}
data G = G ![Int] !W

{-@ needTiny :: {v : W | wOf v <= 3} -> Int @-}
needTiny :: W -> Int
needTiny (W n) = n

useG :: G -> Int
useG (G _ w) = needTiny w
