module SetUnionTextFieldGood (Names (..), combine, names) where

import qualified Data.Set as Set
import Data.Text (Text)

data Names = Names !(Set.Set Text)

{-@ data Names where
      Names :: Set.Set {t:Text | tvalid t} -> Names @-}

{-@ measure names @-}
names :: Names -> Set.Set Text
names (Names s) = s

combine :: Names -> Names -> Names
combine (Names a) (Names b) = Names (Set.union a b)
