module MapCompositionFalse where

import Data.Map.Strict (Map)
import Data.Set (Set)
import MapCompositionLaws (tableUnionRows, unionComm)

{-@ bad :: a:Map Integer (Set Integer) -> b:Map Integer (Set Integer) -> {u:() | tableUnionRows a b == a} @-}
bad :: Map Integer (Set Integer) -> Map Integer (Set Integer) -> ()
bad a b = unionComm a b
