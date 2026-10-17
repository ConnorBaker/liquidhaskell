module TextStripPrefixFalse where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ unchanged :: p:{Text | tvalid p} -> t:{Text | tvalid t}
      -> Maybe {r:Text | tbytes r == tbytes t} @-}
unchanged :: Text -> Text -> Maybe Text
unchanged p t = Text.stripPrefix p t
