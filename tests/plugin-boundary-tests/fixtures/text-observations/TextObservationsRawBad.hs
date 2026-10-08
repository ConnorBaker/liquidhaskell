module TextObservationsRawBad where

import Data.Text (Text)
import Data.Text qualified as Text

rawUncons :: Text -> Maybe (Char, Text)
rawUncons text = Text.uncons text
