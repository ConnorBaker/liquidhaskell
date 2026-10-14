module TextGeneratedOrdBad where

import Data.Text (Text)

-- GHC binds the Ord [Text] dictionary as a generated top-level binder. Its
-- obligation on the bounded Ord Text instance belongs to the comparison.
before :: [Text] -> [Text] -> Bool
before l r = l < r
