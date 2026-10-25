module TextToLowerVacuity where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ neverEmpty :: t:{Text | tvalid t} -> {v:Bool | false} @-}
neverEmpty :: Text -> Bool
neverEmpty t = Text.null (Text.toLower t)
