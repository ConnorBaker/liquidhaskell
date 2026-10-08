module TextAppendRawRightBad where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ disproved :: {x:Text | tvalid x && tbytes x == 0} -> Text -> Text @-}
disproved :: Text -> Text -> Text
disproved = Text.append
