-- Every Text is bounded, so Set.union needs no further Text domain.
module SetUnionTextMeasureGood (combine) where

import qualified Data.Set as Set
import Data.Text (Text)

{-@ measure okT :: Text -> Bool @-}

{-@ combine :: Set.Set {t:Text | okT t} -> Set.Set {t:Text | okT t} -> Set.Set {t:Text | okT t} @-}
combine :: Set.Set Text -> Set.Set Text -> Set.Set Text
combine a b = Set.union a b
