module SetUnionTextVarianceGood (combine) where

import qualified Data.Set as Set
import Data.Text (Text)

{-@ data variance Set.Set covariant @-}

{-@ combine :: Set.Set {t:Text | tvalid t} -> Set.Set {t:Text | tvalid t} -> Set.Set {t:Text | tvalid t} @-}
combine :: Set.Set Text -> Set.Set Text -> Set.Set Text
combine a b = Set.union a b
