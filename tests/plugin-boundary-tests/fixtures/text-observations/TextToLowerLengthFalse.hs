module TextToLowerLengthFalse where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ sameLength :: t:{Text | tvalid t} -> {v:Text | tvalid v && tlen v == tlen t} @-}
sameLength :: Text -> Text
sameLength t = Text.toLower t
