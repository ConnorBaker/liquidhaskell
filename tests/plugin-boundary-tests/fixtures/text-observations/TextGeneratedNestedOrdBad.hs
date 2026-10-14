module TextGeneratedNestedOrdBad where

import Data.Text (Text)

-- The Ord [Text] dictionary is used only by the generated Ord [[Text]]
-- dictionary, which the comparison uses.
before :: [[Text]] -> [[Text]] -> Bool
before l r = l < r
