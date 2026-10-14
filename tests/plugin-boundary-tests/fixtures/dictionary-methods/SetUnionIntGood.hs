-- Ord Int's max contract returns one of its arguments, so the instance
-- inhabits Ord at any refinement of Int.
module SetUnionIntGood (combine) where

import qualified Data.Set as Set

{-@ combine :: Set.Set {t:Int | t > 0} -> Set.Set {t:Int | t > 0} -> Set.Set {t:Int | t > 0} @-}
combine :: Set.Set Int -> Set.Set Int -> Set.Set Int
combine a b = Set.union a b
