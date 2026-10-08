module TextIngressRawBad where

import Data.Text (Text)

{-@ data DecodedText where
      DecodedText :: {text:Text | tvalid text} -> DecodedText
  @-}
data DecodedText = DecodedText !Text

raw :: Text -> DecodedText
raw text = DecodedText text
