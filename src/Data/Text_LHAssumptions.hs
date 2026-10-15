{-# LANGUAGE CPP #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}

module Data.Text_LHAssumptions where

#include "MachDeps.h"

import Data.Maybe_LHAssumptions ()
import Data.Primitive.ByteArray (ByteArray, sizeofByteArray)
import Data.Text (Text, append, drop, empty, length, null, pack, singleton, span, split, uncons)
import qualified Data.Text.Internal
import qualified Data.Text.Unsafe
import Data.Tuple_LHAssumptions ()

{-@ LIQUID "--higherorder" @-}

#if WORD_SIZE_IN_BITS == 32
{-@ expression TextMaxInt = 2147483647 @-}
#elif WORD_SIZE_IN_BITS == 64
{-@ expression TextMaxInt = 9223372036854775807 @-}
#else
#error Unsupported GHC target Int width
#endif

-- Text has two independent domain obligations. For Text array offset bytes,
-- tbounds means 0 <= offset, 0 <= bytes, offset <= sizeof(array), and
-- bytes <= sizeof(array) - offset. Under tbounds, tutf8 means the slice is a
-- complete, well-formed UTF-8 sequence. No bounds follow from tutf8 alone;
-- its interpretation outside a bounded slice supplies no content facts.
-- tvalid names their conjunction, the domain of Unicode observations.
-- tbounds is text's own representation invariant: its constructor requires a
-- bounded slice, as do the unsafe slicing operations below, so every Text is
-- bounded. Validity is not an invariant: raw constructors and unsafe
-- operations may form malformed UTF-8. Producers establish tutf8 and tvalid.
--
-- On bounded slices, tbytes is the stored byte length. On valid slices, tlen
-- counts Unicode scalar values; thead denotes the first only when tlen is
-- positive. The scalar/byte conservation laws require both predicates.
-- These are observations of the sequence, not a definition of content equality.
-- text-2.1's slice representation bounds tbytes by the target's maximum Int;
-- each scalar occupies between one and four bytes. Growing operations need
-- explicit capacity and valid inputs; no arbitrary IsString/Semigroup instance
-- is admitted by these contracts.
{-@
measure tbounds :: Text -> Bool
measure tutf8 :: Text -> Bool
measure tvalid :: Text -> Bool
measure tlen :: Text -> Int
measure tbytes :: Text -> Int
measure thead :: Text -> Char

// Metadata observation only: sizeofByteArray does not index the allocation.
opaque-reflect Data.Primitive.ByteArray.sizeofByteArray
assume Data.Primitive.ByteArray.sizeofByteArray
  :: array:ByteArray
  -> {n:Nat | n == Data.Primitive.ByteArray.sizeofByteArray array}

// The constructor requires a bounded slice (text's documented invariant);
// it does not validate UTF-8.
data Text where
  Data.Text.Internal.Text
    :: array:ByteArray
    -> offset:{Int | 0 <= offset && offset <= Data.Primitive.ByteArray.sizeofByteArray array}
    -> bytes:{Int | 0 <= bytes && bytes <= Data.Primitive.ByteArray.sizeofByteArray array - offset}
    -> {t:Text | tbytes t == bytes && tbounds t}

invariant {t:Text | tbounds t}

invariant {t:Text | tvalid t <=> (tbounds t && tutf8 t)}

invariant {t:Text | tbounds t => (0 <= tbytes t && tbytes t <= TextMaxInt)}

invariant {t:Text | tvalid t =>
  (0 <= tlen t && tlen t <= tbytes t && tbytes t <= 4 * tlen t
              && tbytes t <= TextMaxInt)}

assume Data.Text.empty :: {t:Text | tvalid t && tlen t == 0 && tbytes t == 0}

// In text's non-developer build, null only compares the stored byte length
// with zero (Data/Text.hs:576-582); it does not decode or dereference the slice.
// Only its relationship to the Unicode count requires a valid slice.
assume Data.Text.null
  :: t:Text -> {v:Bool | tvalid t => (v <=> tlen t == 0)}

@-}

-- text-2.1.3 Data/Text/Show.hs:145-159 implements singleton by sanitizing one
-- character, allocating its exact UTF-8 width, writing it, and freezing the
-- array. ASCII is unchanged and occupies one byte. This deliberately admits
-- only that bounded character domain, not arbitrary primitive Char values.
-- Data/Text/Internal.hs:89-103 implements append by returning an operand when
-- the other is empty, otherwise allocating the byte sum and copying both
-- bounded slices. The dependent bound excludes its size-overflow branch.
-- text-2.1.3 Data/Text/Internal.hs:245-272 implements pack by writing each
-- sanitized character (safe) as UTF-8 into a growing buffer, then shrinking
-- it to the bytes written; pack [] is empty. Its result is bounded and valid.
-- The owners here are NOINLINE (pack until phase 0): these contracts state the
-- functions' own definitions, not the literal rules in Data/Text/Show.hs:145-155 that
-- replace pack on literals, and grant no validity to unchecked addresses.
{-@
assume Data.Text.singleton
  :: c:{Char | (lit "0" Char) <= c && c <= (lit "127" Char)}
  -> {t:Text | tvalid t && tlen t == 1 && tbytes t == 1 && thead t == c}

assume Data.Text.pack :: String -> {t:Text | tvalid t}

assume Data.Text.append
  :: x:{Text | tvalid x}
  -> y:{Text | tvalid y && tbytes y <= TextMaxInt - tbytes x}
  -> {t:Text | tvalid t && tbytes t == tbytes x + tbytes y
                        && tlen t == tlen x + tlen y}
@-}

-- Text's Ord instance inherits the base defaults: min/max return an original
-- argument, not merely an Eq-equal replacement. This is instance-specific;
-- compareText compares bounded byte slices without decoding UTF-8. Its
-- unchecked array comparison still requires bounds, but not tutf8. Returning
-- an input preserves that input's properties; it does not validate its bytes.
-- Every Text is bounded, so Ord needs no further domain.
{-@
instance Ord Text where
  assume min :: x:Text -> y:Text -> {v:Text | v == x || v == y}
  assume max :: x:Text -> y:Text -> {v:Text | v == x || v == y}
@-}

-- text-2.1.3 Data/Text/Unsafe.hs:150-165: lengthWord8 reads the stored byte
-- length; takeWord8 and dropWord8 slice without checking, keeping their
-- argument's array and adjusting offset and length by k. unsafeTail (59-66)
-- drops the first scalar's leader-declared width, which is within the slice
-- only for a valid nonempty Text. These preconditions keep the constructor's
-- bounded-slice invariant.
{-@
assume Data.Text.Unsafe.takeWord8
  :: k:Int -> t:{Text | 0 <= k && k <= tbytes t} -> {v:Text | tbytes v == k}
assume Data.Text.Unsafe.dropWord8
  :: k:Int -> t:{Text | 0 <= k && k <= tbytes t} -> {v:Text | tbytes v == tbytes t - k}
assume Data.Text.Unsafe.unsafeTail
  :: t:{Text | tvalid t && 0 < tbytes t} -> {v:Text | tbytes v < tbytes t}

assume Data.Text.Unsafe.lengthWord8 :: t:Text -> {v:Int | v == tbytes t}
@-}

-- text-2.1.3 Data/Text/Internal.hs:116-130: the exported smart constructor
-- text (and its deprecated alias textP) returns empty for a zero length and
-- otherwise builds the slice without checking it, so it needs the
-- constructor's bounded-slice precondition.
{-@
assume Data.Text.Internal.text
  :: array:ByteArray
  -> offset:{Int | 0 <= offset && offset <= Data.Primitive.ByteArray.sizeofByteArray array}
  -> bytes:{Int | 0 <= bytes && bytes <= Data.Primitive.ByteArray.sizeofByteArray array - offset}
  -> {t:Text | tbytes t == bytes}

assume Data.Text.Internal.textP
  :: array:ByteArray
  -> offset:{Int | 0 <= offset && offset <= Data.Primitive.ByteArray.sizeofByteArray array}
  -> bytes:{Int | 0 <= bytes && bytes <= Data.Primitive.ByteArray.sizeofByteArray array - offset}
  -> {t:Text | tbytes t == bytes}
@-}

-- text-2.1.3 Data/Text.hs:627 defines length as negate . measureOff maxBound.
-- measureOff returns a positive byte offset when that many scalars exist
-- (Data/Text.hs:1340-1352; cbits/measure_off.c:200-228). At exactly TextMaxInt
-- scalars the capacity bound forces all bytes to be ASCII, giving -TextMaxInt,
-- not the denotational count. Do not discard this endpoint from tvalid.
{-@
assume Data.Text.length
  :: t:{Text | tvalid t}
  -> {v:Int | v == (if tlen t < TextMaxInt then tlen t else 0 - tlen t)}

assume Data.Text.uncons
  :: t:{Text | tvalid t}
  -> {v:Maybe ({c:Char | c == thead t},
              {r:Text | tvalid r && tlen r + 1 == tlen t
                     && 1 <= tbytes t - tbytes r
                     && tbytes t - tbytes r <= 4})
      | isJust v <=> tlen t > 0}

assume Data.Text.span
  :: p:(Char -> Bool)
  -> t:{Text | tvalid t}
  -> (prefix :: {v:Text | tvalid v
        && (tlen t > 0 => (tlen v > 0 <=> p (thead t)))
        && (tlen v > 0 => thead v == thead t)},
      {v:Text | tvalid v
        && tlen prefix + tlen v == tlen t
        && tbytes prefix + tbytes v == tbytes t
        && (tlen v > 0 => not (p (thead v)))
        && (tlen prefix == 0 && tlen t > 0 => thead v == thead t)})

assume Data.Text.drop
  :: n:Int
  -> t:{Text | tvalid t}
  -> {v:Text | tvalid v
      && (n <= 0 => tlen v == tlen t)
      && (0 < n && n < tlen t => tlen v == tlen t - n)
      && (0 < n && tlen t <= n => tlen v == 0)
      && tlen t - tlen v <= tbytes t - tbytes v
      && tbytes t - tbytes v <= 4 * (tlen t - tlen v)
      && (n <= 0 && tlen t > 0 => thead v == thead t)}
@-}

-- text-2.1.3's split uses span_ and removes one scalar from each nonempty
-- remainder before recurring. Both pieces of span_ are valid slices; removing
-- that scalar preserves validity and strictly decreases the remaining tlen.
-- The empty input produces [empty]. This is character-predicate splitting,
-- not the multi-byte-pattern search and unchecked index advances of splitOn.
{-@
assume Data.Text.split
  :: (Char -> Bool)
  -> {t:Text | tvalid t}
  -> [{piece:Text | tvalid piece}]
@-}
