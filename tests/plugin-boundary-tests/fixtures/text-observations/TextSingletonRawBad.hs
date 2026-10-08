module TextSingletonRawBad where

import Data.Text (Text)
import Data.Text qualified as Text

-- The narrow producer requires an ASCII argument, not an arbitrary Char.
disproved :: Char -> Text
disproved = Text.singleton
