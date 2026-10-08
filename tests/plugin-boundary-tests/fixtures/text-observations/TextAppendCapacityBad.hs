module TextAppendCapacityBad where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ disproved :: {x:Text | tvalid x} -> {y:Text | tvalid y} -> Text @-}
disproved :: Text -> Text -> Text
disproved = Text.append
