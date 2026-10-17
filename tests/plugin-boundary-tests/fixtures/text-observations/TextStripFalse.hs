module TextStripFalse where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ sameLength :: t:{Text | tvalid t} -> {v:Text | tlen v == tlen t} @-}
sameLength :: Text -> Text
sameLength t = Text.strip t
