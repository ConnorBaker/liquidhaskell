module TextRawNotBoundsBad where

import Data.Text (Text)

{-@ disproved :: Text -> {v:Text | tbounds v} @-}
disproved :: Text -> Text
disproved text = text
