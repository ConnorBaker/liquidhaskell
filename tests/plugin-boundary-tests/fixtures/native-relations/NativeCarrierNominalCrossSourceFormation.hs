module NativeCarrierNominalCrossSourceFormation where

import Data.Kind (Type)

data Map (k :: Type) (v :: Type) = M
data Arr (k :: Type) (v :: Type) = A

{-@ embed Map as Map_t @-}
{-@ embed Arr as Array_t @-}

{-@ witness :: m:Map Int Bool -> a:Arr Int Bool
            -> {v:() | (m == a) => (a == m)} @-}
witness :: Map Int Bool -> Arr Int Bool -> ()
witness _ _ = ()
