module TextAppendRawLeftBad where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ disproved :: Text -> {y:Text | tvalid y && tbytes y == 0} -> Text @-}
disproved :: Text -> Text -> Text
disproved = Text.append
