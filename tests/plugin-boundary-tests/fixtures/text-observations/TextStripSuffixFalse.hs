module TextStripSuffixFalse where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ rawValid :: p:Text -> t:{Text | tvalid t}
      -> Maybe {r:Text | tvalid r} @-}
rawValid :: Text -> Text -> Maybe Text
rawValid p t = Text.stripSuffix p t
