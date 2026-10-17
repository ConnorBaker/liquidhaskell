module TextStripRawBad where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ rawStrip :: t:Text -> Text @-}
rawStrip :: Text -> Text
rawStrip t = Text.strip t
