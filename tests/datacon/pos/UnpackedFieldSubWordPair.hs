{-# OPTIONS_GHC -O1 #-}

-- | A sub-word leaf INSIDE an @{-\# UNPACK \#-}@ed two-field product.
--
-- @P@ is @P !Word8 !Int@, and @D@'s first field is an @{-\# UNPACK \#-}@ed
-- @!P@, so that field stands on TWO worker arguments, a @Word8#@ and an
-- @Int#@, and its shape is a 'Product' whose rebuild is @P y z@. This is the
-- measurement behind the sentence in 'RepMap''s documentation of
-- 'frLeafResorted':
--
-- > Always 'False' for a 'Product', whose constructor takes its leaves at the
-- > worker's sorts by construction, and for an unresorted 'Atom'.
--
-- 'frLeafResorted' is decided in the 'Atom' case only, from the sort of the
-- one argument against the type it stands for; a product standing on several
-- arguments is not marked resorted because one of its leaves is at a sort of
-- its own. Inside @P@, the @!Word8@ field IS the sub-word 'Atom' of
-- @UnpackedFieldSubWord.hs@ and loses its selector; @D@'s @dP@ keeps its
-- selector, with @sel (D y z n) = P y z@ stated at the worker's sorts, and
-- 'dN' is proven through a construction.
--
-- Measured at @-O1@: against the series tip @Illegal type specification for
-- `P`@ -- @Cannot unify int with GHC.Internal.Prim.Word8# in expression:
-- P##lqdc##$select##P##1 VV == lqdc##$select##P##1##P@, the kept selector of
-- @P@'s own @Word8@ field, so the tip is rejected at the INNER constructor
-- before @D@'s product field is reached at all; here @SAFE (1 constraints
-- checked)@; against the series base (3a9bcadd) also @SAFE (1)@. So on this
-- shape the fix is back to the base's verdict at an identical count, and the
-- module is red on the tip for the 'Atom' seam, not for anything about the
-- product.
--
-- What this module does NOT do, stated so nobody reads more into its green: a
-- mutant marking the 'Product' resorted was not run against it. Such a mutant
-- drops @dP@'s selector, and nothing here reads @dP@, so the sentence above is
-- what this module MEASURES rather than a claim it would catch being false.
--
-- The companion negative is @tests/datacon/neg/UnpackedFieldSubWordPair.hs@.
module UnpackedFieldSubWordPair where

import Data.Word (Word8)

data P = P !Word8 !Int

data D = D { dP :: {-# UNPACK #-} !P, dN :: !Int }

{-@ measure dN @-}

{-@ mk :: P -> n:Int -> {v:D | dN v == n} @-}
mk :: P -> Int -> D
mk p n = D p n
