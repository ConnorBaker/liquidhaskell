module SetCompositionBad where

import qualified Data.Set as Set

{-@ isEmpty :: xs:Set.Set Int -> {v:Bool | v <=> Set_emp xs} @-}
isEmpty :: Set.Set Int -> Bool
isEmpty = not . Set.null
