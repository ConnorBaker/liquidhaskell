module TextPackGood where

import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text

{-@ packed :: String -> {t:Text | tvalid t} @-}
packed :: String -> Text
packed = Text.pack

-- Ord Text requires bounded elements; packed names are valid.
names :: [String] -> Set.Set Text
names = Set.fromList . map Text.pack
