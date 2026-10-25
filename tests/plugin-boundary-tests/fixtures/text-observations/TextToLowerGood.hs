module TextToLowerGood where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ lowered :: t:{Text | tvalid t} -> {v:Text | tvalid v} @-}
lowered :: Text -> Text
lowered t = Text.toLower t

-- The valid result is usable where a valid Text is required.
{-@ loweredAfter :: p:{Text | tvalid p} -> t:{Text | tvalid t} -> Maybe {r:Text | tvalid r} @-}
loweredAfter :: Text -> Text -> Maybe Text
loweredAfter p t = Text.stripPrefix p (Text.toLower t)
