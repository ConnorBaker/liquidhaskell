module TextOrdRawCompareBad where

import Data.Text (Text)

choose :: Text -> Text -> Ordering
choose = compare
