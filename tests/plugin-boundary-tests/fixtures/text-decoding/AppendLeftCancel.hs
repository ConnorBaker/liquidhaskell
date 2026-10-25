module AppendLeftCancel where

import Data.Text (Text)
import qualified Data.Text as Text

{-@ type Part = {t:Text | tvalid t && tbytes t <= 4096} @-}

{-@ leftCancel :: x:Part -> y:Part -> z:Part -> {v:() | Text.append x y == Text.append x z => y == z} @-}
leftCancel :: Text -> Text -> Text -> ()
leftCancel x y z =
  Text.append x y `seq` Text.append x z `seq`
    ()
