module TextStripPrefixRawBad where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ rawPrefix :: p:{Text | tvalid p} -> t:Text -> Maybe Text @-}
rawPrefix :: Text -> Text -> Maybe Text
rawPrefix p t = Text.stripPrefix p t
