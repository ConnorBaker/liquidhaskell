module SetUnionIntFalse (combine) where

import qualified Data.Set as Set

{-@ combine :: Set.Set {t:Int | t > 0} -> Set.Set {t:Int | t > 0} -> Set.Set {t:Int | t > 0} @-}
combine :: Set.Set Int -> Set.Set Int -> Set.Set Int
combine a _ = Set.union a (Set.singleton 0)
