{-# OPTIONS_GHC -O1 #-}

-- | The newtype-chain twin of @UnpackedFieldSubWord.hs@: GHC unpacks
-- @!P8@ THROUGH the newtype to the @Word8@ under it and then to that
-- @Word8#@, so the field's 'frVia' is @[P8]@ and its one worker argument is a
-- @Word8#@ while the chain LANDED on @Word8@, which embeds to @int@.
--
-- Here the rebuild is not the identity but @P8 y@, and @P8@ is a constructor
-- the logic knows -- so a rebuildability test that asks only "is every
-- constructor known" says yes, keeps the selector, and declares
-- @sel (D y) = P8 y@, which hands @P8 : func([int; P8])@ a @Word8#@. Measured
-- at @-O2@ against the series tip: @Illegal type specification for `D`@,
-- @Cannot unify int with GHC.Internal.Prim.Word8# in expression: P8
-- lqdc##$select##D##1##D@; against the series base, @SAFE (1)@. So the sort
-- the leaf is compared against is the type the chain landed on, not the
-- field's own type: 'frLeafResorted' is @sortOf Word8 /= sortOf Word8#@ here,
-- where 'frResorted' (@sortOf P8 /= sortOf Word8#@) is true of @newtype Pos =
-- Pos Int@ over an @Int#@ as well, whose @Pos y@ IS well sorted and must keep
-- its selector (@pos/NewtypeFieldReftPle.hs@).
module UnpackedFieldSubWordNewtype where

import Data.Word (Word8)

newtype P8 = P8 Word8

data D = D { dP :: !P8, dN :: !Int }

{-@ measure dN @-}

{-@ mk :: P8 -> n:Int -> {v:D | dN v == n} @-}
mk :: P8 -> Int -> D
mk p n = D p n
