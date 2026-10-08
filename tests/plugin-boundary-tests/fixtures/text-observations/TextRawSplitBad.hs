module TextRawSplitBad where

import Data.Text (Text)
import Data.Text qualified as Text

rawSplit :: Text -> [Text]
rawSplit text = Text.split (== '/') text
