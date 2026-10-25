module DecodedSize where

import Data.ByteString (ByteString)
import Data.Text (Text)
import Data.Text.Encoding (decodeUtf8With)
import Data.Text.Encoding.Error (lenientDecode)

{-@ sizedDecode :: bytes:ByteString -> {v:Text | tbytes v == bslen bytes} @-}
sizedDecode :: ByteString -> Text
sizedDecode bytes =
  decodeUtf8With lenientDecode bytes
