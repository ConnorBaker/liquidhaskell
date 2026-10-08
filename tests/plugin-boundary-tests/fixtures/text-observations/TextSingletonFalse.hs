module TextSingletonFalse where

import Data.Text (Text)
import Data.Text qualified as Text

{-@ disproved :: {t:Text | tvalid t && tbytes t == 2} @-}
disproved :: Text
disproved = Text.singleton 's'
