{-# LANGUAGE ImportQualifiedPost #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskellBoot #-}

module Data.Text.Encoding_LHAssumptions where

import Data.ByteString (ByteString)
import qualified Data.ByteString
import Data.ByteString_LHAssumptions ()
import Data.Text (Text)
import Data.Text.Encoding (decodeASCII', decodeUtf8', encodeUtf8)
import Data.Text.Encoding.Error (UnicodeException)
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
