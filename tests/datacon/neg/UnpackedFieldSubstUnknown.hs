{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=has no selector in the logic" @-}

-- | The 'unpackedFieldSubst' twin of @NestedCaseProjectionUnknown.hs@, and
-- the shape that showed the selector table alone is not the whole refusal.
--
-- @A2@'s strict @IORef@ field unpacks to a @MutVar#@ through @IORef@ and
-- @STRef@, neither of which the logic knows, so the field has no selector.
-- The Core body of 'a2R' is @IORef (STRef mv)@ -- the newtype constructor
-- applied by the cast -- and rewriting @mv@ to @STRef.sel1 (IORef.sel1 r)@
-- gives an eta redex 'etaCollapse' cancels ALL the way back to the source
-- binder @r@. The equation names no selector at all, so the selector check
-- passes; what fails, later, is 'toWorkerDef' substituting the rebuild
-- @IORef (STRef y)@ for @r@ and the declaration being rejected with
-- @Unbound symbol GHC.Internal.IORef.IORef@. Measured before the second
-- refusal existed. 'keepsUnrebuildable' refuses here instead, at the
-- measure, naming the field.
module UnpackedFieldSubstUnknown where

import Data.IORef (IORef)

data A2 = A2 !(IORef Int)

{-@ measure a2R @-}
a2R :: A2 -> IORef Int
a2R (A2 r) = r
