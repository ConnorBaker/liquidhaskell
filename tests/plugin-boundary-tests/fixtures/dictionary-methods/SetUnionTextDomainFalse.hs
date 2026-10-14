-- Text's Ord methods require tbounds arguments, which okT does not imply.
module SetUnionTextDomainFalse (combine) where

import qualified Data.Set as Set
import Data.Text (Text)

{-@ measure okT :: Text -> Bool @-}

{-@ combine :: Set.Set {t:Text | okT t} -> Set.Set {t:Text | okT t} -> Set.Set {t:Text | okT t} @-}
combine :: Set.Set Text -> Set.Set Text -> Set.Set Text
combine a b = Set.union a b
