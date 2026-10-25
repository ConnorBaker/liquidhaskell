module ComposedOrderGood where

import Data.Text (Text)
import qualified Data.Text as Text

{-@ type Part = {t:Text | tvalid t && tbytes t <= 4096} @-}

{-@ path :: dsep:Char -> nsep:Char -> dir:Part -> hash:Part -> name:Part
         -> {v:Text | v == Text.append dir (Text.append (Text.singleton dsep)
                              (Text.append hash (Text.append (Text.singleton nsep) name)))
                   && tlen v == tlen dir + tlen hash + tlen name + 2} @-}
path :: Char -> Char -> Text -> Text -> Text -> Text
path dsep nsep dir hash name =
  Text.append dir (Text.append (Text.singleton dsep) (Text.append hash (Text.append (Text.singleton nsep) name)))
