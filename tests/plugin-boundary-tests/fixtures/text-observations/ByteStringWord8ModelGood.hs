module ByteStringWord8ModelGood where

import Data.ByteString (ByteString)
import Data.ByteString qualified as ByteString
import Data.Word (Word8)

-- This owned model uses Word8's numeric interpretation. The imported opaque
-- unpack observation must publish the same list-element sort, without a local
-- restatement or cast of that observation.
{-@ reflect byteModel @-}
{-@ byteModel :: bytes:[Word8] -> {out:[Word8] | len out == len bytes} / [len bytes] @-}
byteModel :: [Word8] -> [Word8]
byteModel [] = []
byteModel (byte : rest) = byte : byteModel rest

{-@ observedModel :: bytes:ByteString
      -> {out:[Word8] | out == byteModel (ByteString.unpack bytes)} @-}
observedModel :: ByteString -> [Word8]
observedModel bytes = byteModel (ByteString.unpack bytes)
