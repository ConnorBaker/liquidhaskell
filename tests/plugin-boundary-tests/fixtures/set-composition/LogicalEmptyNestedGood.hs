module LogicalEmptyNestedGood where

import Data.Set (Set)

{-@ emptySubset :: input:Set a -> {v:() | Set_sub (Set_cup (Set_empty 0) (Set_empty 0)) input} @-}
emptySubset :: Set a -> ()
emptySubset _ = ()
