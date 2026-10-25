module TextToLowerRawBad where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ rawLower :: t:Text -> Text @-}
rawLower :: Text -> Text
rawLower t = Text.toLower t
