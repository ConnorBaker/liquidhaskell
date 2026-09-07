{-# OPTIONS_GHC -O1 #-}

-- | The MULTI-component twin of @UnpackedFieldReftSort.hs@: a field that
-- expands to SEVERAL components keeps its refinement too.
--
-- @H@'s second field carries an explicit @{-# UNPACK #-}@ over a two-field
-- product, so the worker takes two @Int@s where the spec is written at @P2@.
-- 'mkProductTy''s multi-component branch gave every component @ofType@, which
-- carries a TRIVIAL refinement, so @{v : P2 | p2Fst v <= 10}@ was dropped
-- outright -- and unlike the single-component branch, nothing in the source
-- admitted it. Measured before the fix, on this module: @SAFE (1)@ at @-O0@,
-- @UNSAFE (1)@ at @-O1@ and @-O2@, at an IDENTICAL constraint count.
--
-- The refinement relates ALL the components at once, so it cannot sit on any
-- one of them in isolation. It goes on the LAST, which is the only position
-- where every earlier binder is in scope: a constructor's spec is a dependent
-- function type, so an argument's refinement may name the arguments before it.
-- What is stated on the second component is @{v : int | p2Fst (P2 a v) <= 10}@.
--
-- @tests/datacon/pos/UnpackedFieldReftMulti3.hs@ is the three-component
-- version, where the field is not last in the record either, so the attachment
-- has both an earlier binder and a later field to get wrong. The companion
-- negative demands MORE than the bound gives; without it this module is
-- discharged just as well by a rebuild asserting @true@, which is what the
-- previous behaviour did.
module UnpackedFieldReftMulti where

data P2 = P2 !Int !Int

{-@ measure p2Fst @-}
p2Fst :: P2 -> Int
p2Fst (P2 a _) = a

{-@ data H = H [Int] {v : P2 | p2Fst v <= 10} @-}
data H = H ![Int] {-# UNPACK #-} !P2

{-@ needSmall :: {v : P2 | p2Fst v <= 10} -> Int @-}
needSmall :: P2 -> Int
needSmall (P2 a _) = a

useH :: H -> Int
useH (H _ p) = needSmall p
