{-# OPTIONS_GHC -O1 #-}
-- Companion to tests/datacon/pos/UnpackedFieldReftMulti.hs.
--
-- The refinement a multi-component expansion keeps is an EQUALITY with what
-- was written, not a licence. @H@'s field gives @p2Fst v <= 10@ and this
-- module demands @<= 3@ of it, which does not follow.
--
-- This is the arm that makes the positive mean something. A rebuild that
-- asserted @true@ -- or one that dropped the refinement, which is the
-- behaviour before the fix -- would leave the positive @SAFE@ for the wrong
-- reason. It is a GUARD as well: it is UNSAFE before the fix too, since a
-- dropped refinement cannot discharge @<= 3@ either. What it pins is that the
-- fix did not overshoot into asserting the component bound outright.

{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

module UnpackedFieldReftMulti where

data P2 = P2 !Int !Int

{-@ measure p2Fst @-}
p2Fst :: P2 -> Int
p2Fst (P2 a _) = a

{-@ data H = H [Int] {v : P2 | p2Fst v <= 10} @-}
data H = H ![Int] {-# UNPACK #-} !P2

{-@ needTiny :: {v : P2 | p2Fst v <= 3} -> Int @-}
needTiny :: P2 -> Int
needTiny (P2 a _) = a

useH :: H -> Int
useH (H _ p) = needTiny p
