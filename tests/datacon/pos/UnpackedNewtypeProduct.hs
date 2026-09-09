{-# OPTIONS_GHC -O1 #-}

-- | An @{-# UNPACK #-}@ed strict field whose type is a NEWTYPE over a
-- multi-field product. GHC unpacks THROUGH the newtype: @D@'s worker takes
-- @Int# -> Int# -> D@, two arguments for one source field.
--
-- This was a NEGATIVE until the 'RepMap' commit, pinning
-- @Requires 1 fields but given 2@ at the data declaration: two descents
-- decided what the field expands to and disagreed -- 'deepSplitProductType'
-- saw through the newtype and gave the worker's SPEC two arguments, while
-- 'unpackInto' refused newtypes and gave the measure equation ONE, so the
-- same constructor had two arities in one run. There is one descent now.
-- 'RepMap' records the newtype in 'frVia' -- the bang is
-- @HsUnpack (Just co)@ and @co@ names it -- descends into @P2@ underneath,
-- and every consumer reads the same two leaves; the rebuild of the field for
-- the measure equation is @NP (P2 y1 y2)@.
--
-- 'mk' is the claim: the measure reads the FIRST component, so a rebuild that
-- ordered the two leaves wrongly would be well sorted and false, and
-- @tests/datacon/neg/UnpackedNewtypeProduct.hs@ demands the other component
-- to show the equality is not a licence.
--
-- @-O0@ is SAFE too: UNPACK is honoured only from @-O1@ up, so there is no
-- seam.
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
