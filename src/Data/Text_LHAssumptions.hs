{-# LANGUAGE CPP #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}

module Data.Text_LHAssumptions where

#include "MachDeps.h"

import Data.Maybe_LHAssumptions ()
import Data.Primitive.ByteArray (ByteArray, sizeofByteArray)
import Data.Text (Text, append, breakOn, breakOnEnd, count, drop, empty, length, null, pack, singleton, span, split, splitOn, strip, stripPrefix, stripSuffix, toCaseFold, toLower, uncons)
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

-- text-2.1.3 Data/Text/Show.hs:157-171 implements singleton for every Char:
-- it replaces the character with safe c, allocates exactly utf8Length (safe c)
-- bytes, writes that scalar with unsafeWrite, and freezes the array.
-- Data/Text/Internal.hs:146-150 defines safe as c unless
-- ord c .&. 0x1ff800 == 0xd800, and then U+FFFD. Every GHC Char is a code
-- point in [0, 0x10FFFF] (ghc-internal-9.1401 GHC/Internal/Char.hs:17-21, chr
-- rejects larger ordinals; GHC/Internal/Enum.hs:436, maxBound), below 2^21,
-- where that mask test selects exactly the surrogates [0xD800, 0xDFFF].
-- Data/Text/Internal/Encoding/Utf8.hs:71-81 gives the width: 1 below 0x80,
-- 2 below 0x800, 3 below 0x10000, otherwise 4; U+FFFD and the surrogates it
-- replaces both take 3. unsafeWrite (Data/Text/Internal/Unsafe/Char.hs:57-85)
-- writes the standard UTF-8 encoding of the non-surrogate scalar, so the
-- result is one valid scalar.
-- The contract states those cases over the logical Char ordering. They cover
-- every ordinal, but they are true only for code points: it rests on the
-- premise above that c is in [0, 0x10FFFF]. A Char forged with unsafeChr
-- breaks it; for 0x20D800, safe's mask, which ignores bits above 2^21, gives
-- U+FFFD, so singleton writes three bytes (Show.hs:164-170) with head U+FFFD,
-- where the contract states four bytes and thead t == c.
-- Data/Text/Internal.hs:97-111 implements append by returning an operand when
-- the other is empty, otherwise allocating the byte sum and copying both
-- bounded slices. The dependent bound excludes its size-overflow branch.
-- text-2.1.3 Data/Text/Internal.hs:245-272 implements pack by writing each
-- sanitized character (safe) as UTF-8 into a growing buffer, then shrinking
-- it to the bytes written; pack [] is empty. Its result is bounded and valid.
-- singleton (Data/Text/Show.hs:157-171) and append (Data/Text/Internal.hs:97-111)
-- are also opaque reflections, as encodeUtf8 and sizeofByteArray are: each
-- result is the function's own uninterpreted application, so equal arguments
-- give equal results and nothing else is known. That names the order of a
-- composition without a content equation: append a b and append b a are
-- different terms.
-- The owners here are NOINLINE (pack until phase 0): these contracts state the
-- functions' own definitions, not the literal rules in Data/Text/Show.hs:145-155 that
-- replace pack on literals, and grant no validity to unchecked addresses.
{-@
opaque-reflect Data.Text.singleton

assume Data.Text.singleton
  :: c:Char
  -> {t:Text | t == Data.Text.singleton c && tvalid t && tlen t == 1
       && ((c < (lit "128" Char)) => tbytes t == 1)
       && (((lit "128" Char) <= c && c < (lit "2048" Char)) => tbytes t == 2)
       && (((lit "2048" Char) <= c && c < (lit "65536" Char)) => tbytes t == 3)
       && (((lit "65536" Char) <= c) => tbytes t == 4)
       && ((c < (lit "55296" Char) || (lit "57343" Char) < c) => thead t == c)
       && (((lit "55296" Char) <= c && c <= (lit "57343" Char)) => thead t == (lit "65533" Char))}

assume Data.Text.pack :: String -> {t:Text | tvalid t}

opaque-reflect Data.Text.append

assume Data.Text.append
  :: x:{Text | tvalid x}
  -> y:{Text | tvalid y && tbytes y <= TextMaxInt - tbytes x}
  -> {t:Text | t == Data.Text.append x y
                && tvalid t && tbytes t == tbytes x + tbytes y
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

-- text-2.1.3 Data/Text.hs:360-364: Text's (==) is True exactly when the stored
-- byte lengths agree and A.equal finds the two byte slices identical
-- (Data/Text/Array.hs:309-313: compareInternal over that length is 0); it
-- does not compare arrays or offsets. (/=) is the class default.
-- Logical Text values are representations (array, offset, length), so (==)
-- is not their equality: equal content at different offsets compares True.
-- Only what follows from the definition is stated: equal representations
-- compare True, and True means equal byte lengths and identical slices, so
-- equal validity (every Text is bounded, and tutf8 is a property of the
-- slice) and, for valid slices, equal scalar counts.
{-@
instance Eq Text where
  assume (==) :: x:Text -> y:Text
    -> {v:Bool | (x == y => v)
                 && (v => (tbytes x == tbytes y && (tvalid x <=> tvalid y)
                           && (tvalid x => tlen x == tlen y)))}
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

-- text-2.1.3 Data/Text.hs:2027-2030: stripPrefix p t returns, when
-- isPrefixOf p t, the slice of t after plen bytes (Internal.hs:116-130 text).
-- isPrefixOf (1969-1972) compares lengths and then the decoded scalar streams;
-- stream' (Internal/Fusion.hs:101-120) reads a leader's continuation bytes
-- without checking the slice end, so both inputs need valid slices. Equal
-- scalars have equal UTF-8 encodings, so on success the first plen bytes of t
-- are p's bytes and the remainder starts on a scalar boundary.
--
-- stripSuffix (2093-2096) returns the first len - plen bytes of t when
-- isSuffixOf p t, which (1976-1982) compares the last plen bytes of t with p
-- by byte equality (Eq Text, 360-363), within bounds and without decoding.
-- Any bounded inputs are therefore accepted. Only when both are valid does the
-- cut fall on a scalar boundary: a nonempty valid p begins with a leader byte,
-- and a leader byte in valid t begins a scalar.
--
-- toCaseFold (895-898) and toLower (908-912) return empty for empty input,
-- and otherwise caseConvert (Internal/Transformation.hs:82-145) with
-- foldMapping (163-164) or lowerMapping (170-171). caseConvert reads each
-- scalar of a valid slice: an ASCII byte becomes asciiToLower's ASCII byte
-- (181-182), an unmapped scalar keeps its own bytes, and a mapped scalar is
-- replaced by its table entry. writeMapping (147-152) writes each scalar of an
-- entry with unsafeWrite, after chopOffChar (154-159) takes it from 21 bits
-- with chr#. Unlike mapNonEmpty (78), nothing passes these scalars through
-- `safe`. The result is therefore valid only because every entry of the
-- generated tables is a sequence of Unicode scalar values: foldMapping
-- (Internal/Fusion/CaseMapping.hs:4670-7787) and lowerMapping (1674-3138),
-- generated by scripts/CaseMapping.hs from the Unicode 16.0.0 case data
-- (1-6). That table property is the trusted premise of both contracts. A
-- mapping can change the number of scalars and bytes, so no length relation
-- is stated, and nothing relates the result's content to the input's.
--
-- count (1864-1869) raises emptyError on an empty pattern (null compares the
-- stored byte length). A one-scalar pattern is counted by countChar, which
-- streams t; longer patterns by the length of the indices list
-- (Internal/Search.hs:49-56). isSingleton (617-618) streams the pattern. The
-- result is a list length or a count, so it is nonnegative.
{-@
assume Data.Text.stripPrefix
  :: p:{Text | tvalid p}
  -> t:{Text | tvalid t}
  -> Maybe {r:Text | tvalid r
                  && tbytes r == tbytes t - tbytes p
                  && tlen r == tlen t - tlen p}

assume Data.Text.stripSuffix
  :: p:Text
  -> t:Text
  -> Maybe {r:Text | tbytes r == tbytes t - tbytes p
                  && (tvalid p && tvalid t =>
                        (tvalid r && tlen r == tlen t - tlen p))}

assume Data.Text.toCaseFold :: t:{Text | tvalid t} -> {v:Text | tvalid v}

assume Data.Text.toLower :: t:{Text | tvalid t} -> {v:Text | tvalid v}

assume Data.Text.count
  :: pat:{Text | tvalid pat && 0 < tbytes pat}
  -> t:{Text | tvalid t}
  -> {v:Int | 0 <= v}
@-}

-- text-2.1.3 Data/Text.hs:1791-1794: breakOnEnd pat src reverses both inputs,
-- applies breakOn, and reverses the two pieces. reverse (Internal/Reverse.hs:
-- 37-91) copies each scalar by its leader-declared width, so both inputs need
-- valid slices; it returns a valid slice of the same scalars. breakOn
-- (1774-1780) raises emptyError on an empty pattern; otherwise it splits at the
-- first byte match of indices (Internal/Search.hs:49-92), or returns the whole
-- source and empty. The reversed pattern is valid and so begins with a leader
-- byte, and a leader byte in a valid source begins a scalar, so both pieces are
-- valid. Their sizes are not stated.
{-@
assume Data.Text.breakOnEnd
  :: pat:{Text | tvalid pat && 0 < tbytes pat}
  -> src:{Text | tvalid src}
  -> ({v:Text | tvalid v}, {v:Text | tvalid v})
@-}

-- text-2.1.3 Data/Text.hs:1774-1780: breakOn raises emptyError when the
-- pattern's stored byte length is zero; otherwise it searches bytes with
-- indices (Internal/Search.hs:49-92) and slices the source at the first match,
-- or returns the source and empty. Nothing is decoded, so any bounded source
-- is accepted. Only when both inputs are valid does the match, which begins at
-- the pattern's leader byte, fall on a scalar boundary of the source.
--
-- strip (1483-1484) is dropAround isSpace: dropWhile (1434-1440) and
-- dropWhileEnd (1450-1456) decode scalars forward with iter and backward with
-- reverseIter (Unsafe.hs:111-124), reading continuation bytes without checks,
-- so the input must be valid; the result is a slice cut at scalar boundaries.
--
-- splitOn (1652-1666) raises emptyError for an empty pattern, splits on a
-- one-scalar pattern with split, which decodes the source, and otherwise
-- slices at the indices matches. isSingleton (617-618) streams the pattern.
-- Both inputs must be valid; every piece is then a valid slice. Pieces may be
-- empty, and their number is not stated.
{-@
assume Data.Text.breakOn
  :: pat:{Text | 0 < tbytes pat}
  -> src:Text
  -> ({v:Text | tvalid pat && tvalid src => tvalid v},
      {v:Text | tvalid pat && tvalid src => tvalid v})

assume Data.Text.strip :: t:{Text | tvalid t} -> {v:Text | tvalid v}

assume Data.Text.splitOn
  :: pat:{Text | tvalid pat && 0 < tbytes pat}
  -> src:{Text | tvalid src}
  -> [{v:Text | tvalid v}]
@-}
