module TextBreakOnEndRawBad where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ rawSource :: pat:{Text | tvalid pat && 0 < tbytes pat} -> src:Text -> (Text, Text) @-}
rawSource :: Text -> Text -> (Text, Text)
rawSource pat src = Text.breakOnEnd pat src
