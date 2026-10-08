module TextBoundsSplitBad where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ boundedSplit :: {t:Text | tbounds t} -> [Text] @-}
boundedSplit :: Text -> [Text]
boundedSplit text = Text.split (== '/') text
