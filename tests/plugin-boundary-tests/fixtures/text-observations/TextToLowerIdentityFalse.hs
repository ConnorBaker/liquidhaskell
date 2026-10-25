module TextToLowerIdentityFalse where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ unchanged :: t:{Text | tvalid t} -> {v:Text | v == t} @-}
unchanged :: Text -> Text
unchanged t = Text.toLower t
