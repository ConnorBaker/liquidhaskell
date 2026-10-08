module SetCardinalityGood where

import qualified Data.Set as Set

data Element = Element Int

{-@ size :: xs:Set.Set Element -> {v:Int | v == Set_card xs} @-}
size :: Set.Set Element -> Int
size = Set.size
