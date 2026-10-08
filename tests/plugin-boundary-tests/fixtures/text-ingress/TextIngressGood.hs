module TextIngressGood where

import Data.ByteString (ByteString)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Encoding

{-@ data DecodedText where
      DecodedText :: {text:Text | tvalid text} -> DecodedText
  @-}
data DecodedText = DecodedText !Text

empty :: DecodedText
empty = DecodedText Text.empty

decode :: ByteString -> Maybe DecodedText
decode bytes = case Encoding.decodeUtf8' bytes of
    Left _ -> Nothing
    Right text -> Just (DecodedText text)

{-@ contents :: DecodedText -> {text:Text | tvalid text} @-}
contents :: DecodedText -> Text
contents (DecodedText text) = text
