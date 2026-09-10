{-# OPTIONS_GHC -O1 #-}

-- | An @{-\# UNPACK \#-}@ed SUM field beside a measured @Int@.
--
-- GHC unpacks a strict, explicitly unpacked @Maybe Int@ field into an unboxed
-- sum, @(# (# #) | Int #)@, so the worker takes ONE argument for it, at a sort
-- the logic has no name for. The descent finds no single-constructor product
-- to enter -- @Maybe@ has two -- so the field is an 'Atom' with no constructor
-- to rebuild with, and its one worker argument is at another sort than
-- @Maybe Int@ embeds to. That is the seam @UnpackedFieldSubWord.hs@ pins,
-- reached through a sum instead of a sized primitive.
--
-- This module ATTRIBUTES TO THE SERIES, not only to the fix, and that is why it
-- is here rather than as one more sub-word row. Measured at @-O1@, as the
-- suite runs it:
--
--   * against the series tip ("Route the PLE rewrite guards through RepMap"):
--     @Illegal type specification for `D`@, @Cannot unify Maybe with (Sum2#
--     (TupleRep []) (BoxedRep Lifted) Tuple0) in expression:
--     D##lqdc##$select##D##1 VV == lqdc##$select##D##1##D@ -- the KEPT
--     selector's equation stated across the two sorts;
--
--   * here: @SAFE (1 constraints checked)@;
--
--   * against the series base (3a9bcadd, "Keep an unpacked field's
--     refinement, in both expansion branches"), which dropped the selector of
--     every field whose sort moved: ALSO red, with a different error --
--     @Specified type does not refine Haskell type for `D`@, the Liquid type
--     @(# (# #) | 'TupleRep #) -> Int# -> D@ against the Haskell type
--     @(# (# #) | Int #) -> Int# -> D@.
--
-- So on this shape the fix is NOT "back to the base's verdict": the base never
-- accepted it, and 'frLeafResorted' is what makes it verify at all. The
-- companion negative is @tests/datacon/neg/UnpackedFieldSum.hs@.
module UnpackedFieldSum where

data D = D { dM :: {-# UNPACK #-} !(Maybe Int), dN :: !Int }

{-@ measure dN @-}

{-@ mk :: Maybe Int -> n:Int -> {v:D | dN v == n} @-}
mk :: Maybe Int -> Int -> D
mk m n = D m n
