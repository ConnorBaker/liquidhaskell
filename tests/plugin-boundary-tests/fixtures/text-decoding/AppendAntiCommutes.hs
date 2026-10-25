module AppendAntiCommutes where

import Data.Text (Text)
import qualified Data.Text as Text

{-@ type Part = {t:Text | tvalid t && tbytes t <= 4096} @-}

{-@ antiCommutes :: x:Part -> y:Part -> {v:() | Text.append x y /= Text.append y x} @-}
antiCommutes :: Text -> Text -> ()
antiCommutes x y =
  Text.append x y `seq` Text.append y x `seq`
    ()
