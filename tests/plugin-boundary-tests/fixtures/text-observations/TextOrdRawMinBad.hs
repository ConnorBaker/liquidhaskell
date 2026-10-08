module TextOrdRawMinBad where

import Data.Text (Text)

-- Raw Text does not establish even the comparison's bounded-slice domain.
choose :: Text -> Text -> Text
choose = min
