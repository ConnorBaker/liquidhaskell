module OwnedHelperAssumed (ownedNested) where

import OwnedHelperProvider (hydratedHelper, ownedNested)

{-@ ownedNested :: value:Bool -> {result:Bool | result == value} @-}
{-@ assume hydratedHelper :: Bool -> {result:Bool | False} @-}
