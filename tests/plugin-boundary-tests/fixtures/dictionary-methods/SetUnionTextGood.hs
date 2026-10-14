-- Text's refined Ord head requires tbounds arguments; min and max return an
-- argument. Valid Text satisfies both, so no exact element refinement is needed.
module SetUnionTextGood (combine) where

import qualified Data.Set as Set
import Data.Text (Text)

{-@ combine :: Set.Set {t:Text | tvalid t} -> Set.Set {t:Text | tvalid t} -> Set.Set {t:Text | tvalid t} @-}
combine :: Set.Set Text -> Set.Set Text -> Set.Set Text
combine a b = Set.union a b
