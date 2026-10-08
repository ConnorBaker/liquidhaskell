module TextUtf8NotBoundsBad where

import Data.Text (Text)

{-@ disproved :: t:{Text | tutf8 t} -> {v:Text | tbounds v} @-}
disproved :: Text -> Text
disproved text = text
