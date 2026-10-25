module AppendInjective where

import Data.Text (Text)
import qualified Data.Text as Text

{-@ type Part = {t:Text | tvalid t && tbytes t <= 4096} @-}

{-@ injective :: a:Part -> b:Part -> c:Part -> d:Part -> {v:() | Text.append a b == Text.append c d => a == c} @-}
injective :: Text -> Text -> Text -> Text -> ()
injective a b c d =
  Text.append a b `seq` Text.append c d `seq`
    ()
