{-# OPTIONS_GHC -O1 #-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}

-- | The GUARD for @tests/datacon/pos/UnpackedFieldSubWord.hs@, and NOT its
-- attribution: the same record of sub-word fields beside an @Int@, with a
-- claim the measure equation contradicts -- 'bad' returns @tN t@ and claims
-- @v /= tN t@.
--
-- Against the series tip this module is red TOO, with @Illegal type
-- specification for `T`@ at the constructor's own declaration -- the very
-- rejection the positive attributes -- and that text does not match
-- @Liquid Type Mismatch@, so before the fix this module FAILS as a negative
-- (exit 1, no verdict) rather than being discharged by the wrong error. That
-- is why the filter is @--expect-error-containing=Liquid Type Mismatch@ and
-- not @--expect-any-error@, which the defect itself would satisfy. Read a red
-- arm here as "the equation did not become a free pass", never as evidence
-- the fix took effect.
--
-- What it pins after the fix: that the positive's @SAFE@ is a proof and not a
-- vacuous environment. Dropping the seven sub-word selectors took nothing else
-- with it -- the equation over the worker still says what 'tN' reads, and the
-- false claim is caught, @UNSAFE (1 constraints checked)@, against the fix and
-- against the series base alike.
module UnpackedFieldSubWord where

import Data.Int (Int16, Int32, Int64, Int8)
import Data.Word (Word16, Word32, Word64, Word8)

data T = T
  { t8  :: !Word8
  , t16 :: !Word16
  , t32 :: !Word32
  , t64 :: !Word64
  , i8  :: !Int8
  , i16 :: !Int16
  , i32 :: !Int32
  , i64 :: !Int64
  , tN  :: !Int
  }

{-@ measure tN @-}

{-@ bad :: t:T -> {v:Int | v /= tN t} @-}
bad :: T -> Int
bad (T _ _ _ _ _ _ _ _ n) = n
