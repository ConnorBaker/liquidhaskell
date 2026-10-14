module SetInsertIntGood (combine) where

import qualified Data.Set as Set

{-@ combine :: {t:Int | t > 0} -> Set.Set {t:Int | t > 0} -> Set.Set {t:Int | t > 0} @-}
combine :: Int -> Set.Set Int -> Set.Set Int
combine x a = Set.insert x a
