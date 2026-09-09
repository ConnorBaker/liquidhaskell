{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Malformed refined data constructor" @-}

-- | An @{-# UNPACK #-}@ed strict field whose type is a NEWTYPE over a
-- multi-field product. GHC unpacks THROUGH the newtype: @D@'s worker takes
-- @Int# -> Int# -> D@, two arguments for one source field.
--
-- Two descents decide what a field expands to and they disagree here, which
-- is the defect this module pins. 'RefType.mkProductTy' asks
-- 'deepSplitProductType', whose 'topNormaliseType_maybe' sees through the
-- newtype, so the worker's SPEC is two-ary. 'Measure.unpackInto' refuses at
-- @not (isNewTyCon tc)@, so 'fieldRepTys' answers ONE leaf, 'toWorkerDef'
-- cannot rebuild the measure equation over two worker arguments and hands
-- 'stitchArgs' the source-shaped one, and 'Bare.resortedFields' -- arities
-- differ and @regroup [[NP]] [Int#, Int#]@ is 'Nothing' -- answers
-- @replicate 1 False@, KEEPING a selector it cannot declare. The same
-- constructor has two arities in one run.
--
-- The message pinned is what 'stitchArgs' says at the DATA DECLARATION today:
-- @Malformed refined data constructor@. Its second line names the two
-- arities, and WHICH WAY ROUND depends on the command-line optimisation level
-- and not on this module's pragma: @Requires 1 fields but given 2@ under
-- @ghc -O1@, @Requires 2 fields but given 1@ under the suite's @-O0@ with
-- @{-# OPTIONS_GHC -O1 #-}@ here (measured 2026-09-09, four arms varying only
-- the command line and the plugin flags). So the first line is the pin. It
-- names neither the newtype nor the disagreement, which is why a substring
-- and not @--expect-any-error@: a fix that makes the two descents agree turns
-- this module SAFE, and it then moves to @pos@ with 'mk' as its claim.
--
-- @-O0@ is SAFE: UNPACK is honoured only from @-O1@ up, so there is no seam.
module UnpackedNewtypeProduct where

data P2 = P2 !Int !Int

newtype NP = NP P2

data D = D {-# UNPACK #-} !NP

{-@ measure dFst @-}
dFst :: D -> Int
dFst (D (NP (P2 a _))) = a

{-@ mk :: a:Int -> b:Int -> {v:D | dFst v == a} @-}
mk :: Int -> Int -> D
mk a b = D (NP (P2 a b))
