module OwnedHelperBad (ownedNested) where

import OwnedHelperProvider (ownedNested)

{-@ ownedNested :: value:Bool -> {result:Bool | result /= value} @-}
