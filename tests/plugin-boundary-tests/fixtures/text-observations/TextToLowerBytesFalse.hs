module TextToLowerBytesFalse where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ sameBytes :: t:{Text | tvalid t} -> {v:Text | tbytes v == tbytes t} @-}
sameBytes :: Text -> Text
sameBytes t = Text.toLower t
