module TextBoundsFalse where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ boundedUncons :: {t:Text | tbounds t} -> Maybe (Char, Text) @-}
boundedUncons :: Text -> Maybe (Char, Text)
boundedUncons text = Text.uncons text

{-@ comparisonDoesNotValidate
      :: x:{Text | tbounds x} -> y:{Text | tbounds y}
      -> {v:Text | tvalid v} @-}
comparisonDoesNotValidate :: Text -> Text -> Text
comparisonDoesNotValidate left right = min left right
