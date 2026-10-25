{-# LANGUAGE ImportQualifiedPost #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}

module Data.Text.Encoding_LHAssumptions where

import Data.ByteString (ByteString)
import qualified Data.ByteString
import Data.ByteString_LHAssumptions ()
import Data.Text (Text)
import Data.Text.Encoding (decodeASCII', decodeUtf8', decodeUtf8With, encodeUtf8)
import Data.Text.Encoding.Error (OnDecodeError, UnicodeException)
import Data.Text_LHAssumptions ()

-- A trusted contract for text's checked decoder, not for decodeUtf8 or for
-- arbitrary Text constructors. Malformed input is reported on the Left.
-- Internal/Encoding.hs:482-486 copies the whole validated input into Text;
-- incomplete/invalid branches raise strictDecode errors, caught by decodeUtf8'.
{-@
assume Data.Text.Encoding.decodeUtf8'
  :: bs:ByteString -> Either UnicodeException
       {t:Text | tvalid t && tbytes t == bslen bs &&
          Data.ByteString.unpack (Data.Text.Encoding.encodeUtf8 t)
            == Data.ByteString.unpack bs}
@-}

-- On bounded raw Text, J(t) = unpack (encodeUtf8 t) observes representation
-- bytes, not decoded characters. text-2.1.3 Encoding.hs:480-490 allocates the
-- stored byte length and copyI copies exactly that array slice, without UTF-8
-- decoding. Bounds must be established before this unchecked copy.
-- decodeASCII' (Encoding.hs:194-198) copies the ASCII prefix into fresh Text
-- and succeeds only when no suffix remains. Its success preserves every input
-- byte. The length equation alone would not establish content preservation.
{-@
opaque-reflect Data.Text.Encoding.encodeUtf8

assume Data.Text.Encoding.encodeUtf8
  :: t:{Text | tbounds t}
  -> {bs:ByteString | bslen bs == tbytes t &&
       Data.ByteString.unpack bs
         == Data.ByteString.unpack (Data.Text.Encoding.encodeUtf8 t)}

assume Data.Text.Encoding.decodeASCII'
  :: bs:ByteString
  -> Maybe {t:Text | tvalid t && tbytes t == bslen bs && tlen t == bslen bs
       && Data.ByteString.unpack (Data.Text.Encoding.encodeUtf8 t)
            == Data.ByteString.unpack bs}
@-}

-- A second trusted decoder fact: decodeUtf8With returns valid Text for every
-- handler. text-2.1.3 Encoding.hs:355-360 is decodeUtf8With1
-- (Internal/Encoding.hs:477-495). When validateUtf8ChunkFrom accepts all of
-- the input, it returns a copy of the input's bytes (SBS.toShort, :485);
-- otherwise it concatenates byte runs the same validator accepted (also in
-- decodeUtf8With2, Internal/Encoding.hs:505-535) with the handler's
-- replacements. A replacement is SB.fromChar c (handleUtf8Error,
-- Internal/Encoding.hs:465-468), which reserves utf8Length c bytes and writes
-- `safe c` (Internal/StrictBuilder.hs:109-111), and safe maps every surrogate
-- to U+FFFD (Internal.hs:146-149), as decodeUtf8With's documentation states
-- (Encoding.hs:353-354). A handler that throws (strictDecode) returns no Text.
-- The validator is the one decodeUtf8' above rests on. No size is stated:
-- replacements change the byte count.
-- The fact also rests on every replacement Char being a code point, in
-- [0, 0x10FFFF], as every Char that chr builds is (see the premise stated for
-- Data.Text_LHAssumptions' singleton contract). A Char forged above that range
-- with unsafeChr breaks it: 0x110000 is written as a four-byte sequence that
-- encodes no scalar, and 0x20D800 matches safe's surrogate mask, which ignores
-- bits above 2^21, so U+FFFD's three bytes are written into utf8Length's
-- four-byte reservation (Internal/Encoding/Utf8.hs:79-80) and one byte is left
-- unwritten. A negative ordinal, which unsafeChr builds from a negative Int,
-- is outside the range too. Read from source, not run: for unsafeChr (-1),
-- utf8Length's geChar# comparisons choose the width, so unsafeWrite
-- (Internal/Unsafe/Char.hs:62-85) writes EF BF BF BF through ord4 if they
-- compare unsigned, or the lone byte FF if signed; neither is UTF-8.
{-@
assume Data.Text.Encoding.decodeUtf8With
  :: OnDecodeError -> ByteString -> {t:Text | tvalid t}
@-}
