module TextTakeWord8Bad where

import Data.Text (Text)
import Data.Text.Unsafe qualified as Unsafe

-- Taking more bytes than the slice holds would read past it.
overTake :: Text -> Text
overTake text = Unsafe.takeWord8 (Unsafe.lengthWord8 text + 1) text
