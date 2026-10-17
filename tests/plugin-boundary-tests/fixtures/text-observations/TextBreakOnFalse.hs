module TextBreakOnFalse where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ rawValid :: pat:{Text | 0 < tbytes pat} -> src:{Text | tvalid src}
      -> ({v:Text | tvalid v}, Text) @-}
rawValid :: Text -> Text -> (Text, Text)
rawValid pat src = Text.breakOn pat src
