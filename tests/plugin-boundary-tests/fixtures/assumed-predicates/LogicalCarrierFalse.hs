module LogicalCarrierFalse where

import Data.Kind (Type)

data Token a = Token

{-@ measure value :: Token a -> a @-}

{-@ different :: token:Token a -> {v:Bool | value token /= value token} @-}
different :: Token (a :: Type) -> Bool
different _ = True
