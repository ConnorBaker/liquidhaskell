{-# OPTIONS_GHC -O1 #-}

-- | A user-EMBEDDED single-field product that GHC unboxes.
--
-- @Tag@ is a strict one-field product, so @-funbox-small-strict-fields@
-- replaces the @!Tag@ field by the @Int#@ inside it; and @Tag@ is embedded,
-- so the descent stops at it and the field is an 'Atom' with no constructor
-- to rebuild with. Its one worker argument is at @int@ while the field's type
-- embeds to @Tag_t@: the same seam as @UnpackedFieldSubWord.hs@, reached
-- without any primitive type, so it pins the RepMap's decision independently
-- of which unboxed primitives @GHC.Types_LHAssumptions@ happens to embed.
-- Should @Word8#@ and its siblings be embedded to @int@ one day, the sub-word
-- modules stop moving any sort and this one still does.
--
-- Measured at @-O2@: against the series tip @Illegal type specification for
-- `D`@, @Cannot unify Tag_t with int in expression: D##lqdc##$select##D##1
-- VV##0 == lqdc##$select##D##1@; against the series base @SAFE (1)@.
module UnpackedFieldEmbeddedProduct where

data Tag = Tag !Int

{-@ embed Tag as Tag_t @-}

data D = D { dT :: !Tag, dN :: !Int }

{-@ measure dN @-}

{-@ mk :: Tag -> n:Int -> {v:D | dN v == n} @-}
mk :: Tag -> Int -> D
mk t n = D t n
