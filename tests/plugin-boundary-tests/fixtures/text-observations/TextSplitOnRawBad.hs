module TextSplitOnRawBad where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ rawSource :: pat:{Text | tvalid pat && 0 < tbytes pat} -> src:Text -> [Text] @-}
rawSource :: Text -> Text -> [Text]
rawSource pat src = Text.splitOn pat src
