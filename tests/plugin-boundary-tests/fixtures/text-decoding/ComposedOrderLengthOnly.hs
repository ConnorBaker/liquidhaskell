module ComposedOrderLengthOnly where

import Data.Text (Text)
import qualified Data.Text as Text

{-@ type Part = {t:Text | tvalid t && tbytes t <= 4096} @-}

{-@ path :: dsep:Char -> nsep:Char -> dir:Part -> hash:Part -> name:Part
         -> {v:Text | tlen v == tlen dir + tlen hash + tlen name + 2} @-}
path :: Char -> Char -> Text -> Text -> Text -> Text
path dsep nsep dir hash name =
  Text.append name (Text.append (Text.singleton dsep) (Text.append hash (Text.append (Text.singleton nsep) dir)))
