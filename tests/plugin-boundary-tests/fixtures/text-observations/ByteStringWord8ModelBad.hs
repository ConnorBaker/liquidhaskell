module ByteStringWord8ModelBad where

import Data.ByteString (ByteString)
import Data.ByteString qualified as ByteString
import Data.Word (Word8)

{-@ reflect byteModel @-}
{-@ byteModel :: bytes:[Word8] -> {out:[Word8] | len out == len bytes} / [len bytes] @-}
byteModel :: [Word8] -> [Word8]
byteModel [] = []
byteModel (byte : rest) = byte : byteModel rest

-- Empty output cannot conserve the actual observation of a nonempty input.
-- This tests an incorrect owned implementation, not an assume projection.
{-@ observedModel :: bytes:{ByteString | 0 < bslen bytes}
      -> {out:[Word8] | out == byteModel (ByteString.unpack bytes)} @-}
observedModel :: ByteString -> [Word8]
observedModel _bytes = []
