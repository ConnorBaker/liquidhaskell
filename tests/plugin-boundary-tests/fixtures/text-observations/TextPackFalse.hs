module TextPackFalse where

import Data.Text (Text)
import Data.Text qualified as Text

-- pack establishes validity, not a length.
{-@ invented :: String -> {t:Text | tvalid t && tlen t == 0} @-}
invented :: String -> Text
invented = Text.pack
