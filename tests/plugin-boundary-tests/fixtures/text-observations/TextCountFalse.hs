module TextCountFalse where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ present :: pat:{Text | tvalid pat && 0 < tlen pat} -> t:{Text | tvalid t}
      -> {v:Int | 0 < v} @-}
present :: Text -> Text -> Int
present pat t = Text.count pat t
