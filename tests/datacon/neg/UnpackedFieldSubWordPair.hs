{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The negative half of @tests/datacon/pos/UnpackedFieldSubWordPair.hs@: the
-- same two types, with a claim the measure equation contradicts -- 'bad'
-- returns @dN d@ and claims @v /= dN d@. Pins that the positive's @SAFE@ is a
-- proof about 'dN' and not a vacuous environment: dropping the selector of
-- @P@'s @Word8@ field while keeping @D@'s product selector left the equation
-- over the worker saying what 'dN' reads. @UNSAFE (1 constraints checked)@
-- with the fix.
--
-- A GUARD, NOT an attribution: against the series tip this module is rejected
-- at @P@ with @Illegal type specification@, which does not match @Liquid Type
-- Mismatch@, so before the fix it FAILS as a negative (exit 1, no verdict)
-- rather than being discharged by the wrong error.
module UnpackedFieldSubWordPair where

import Data.Word (Word8)

data P = P !Word8 !Int

data D = D { dP :: {-# UNPACK #-} !P, dN :: !Int }

{-@ measure dN @-}

{-@ bad :: d:D -> {v:Int | v /= dN d} @-}
bad :: D -> Int
bad (D _ n) = n
