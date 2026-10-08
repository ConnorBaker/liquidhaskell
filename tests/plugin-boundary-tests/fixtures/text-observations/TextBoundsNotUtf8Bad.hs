module TextBoundsNotUtf8Bad where

import Data.Text (Text)

{-@ disproved :: t:{Text | tbounds t} -> {v:Text | tutf8 v} @-}
disproved :: Text -> Text
disproved text = text
