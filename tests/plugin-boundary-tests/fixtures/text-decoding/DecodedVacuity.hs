module DecodedVacuity where

import Data.ByteString (ByteString)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Text.Encoding (decodeUtf8With)
import Data.Text.Encoding.Error (OnDecodeError)

{-@ falseAfterDecode :: OnDecodeError -> ByteString -> {v:Text | false} @-}
falseAfterDecode :: OnDecodeError -> ByteString -> Text
falseAfterDecode handler bytes =
  Text.strip (decodeUtf8With handler bytes)
