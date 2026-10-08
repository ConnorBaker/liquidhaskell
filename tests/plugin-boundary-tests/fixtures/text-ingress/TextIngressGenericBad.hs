module TextIngressGenericBad where

import Data.Text (Text)
import GHC.Generics (Generic)

{-@ data DecodedText where
      DecodedText :: {text:Text | tvalid text} -> DecodedText
  @-}
data DecodedText = DecodedText !Text deriving (Generic)
