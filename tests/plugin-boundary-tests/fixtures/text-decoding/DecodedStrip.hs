module DecodedStrip where

import Data.ByteString (ByteString)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Text.Encoding (decodeUtf8With)
import Data.Text.Encoding.Error (OnDecodeError, lenientDecode)

lenient :: ByteString -> Text
lenient bytes = Text.strip (decodeUtf8With lenientDecode bytes)

handled :: OnDecodeError -> ByteString -> Text
handled handler bytes = Text.strip (decodeUtf8With handler bytes)
