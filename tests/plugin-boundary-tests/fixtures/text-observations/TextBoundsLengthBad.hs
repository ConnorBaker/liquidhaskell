module TextBoundsLengthBad where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ disproved :: {t:Text | tbounds t} -> Int @-}
disproved :: Text -> Int
disproved text = Text.length text
