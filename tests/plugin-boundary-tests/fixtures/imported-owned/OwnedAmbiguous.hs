module OwnedAmbiguous () where

import OwnedAlternativeProvider (ownedIdentity)
import OwnedIdentityProvider (ownedIdentity)

{-@ ownedIdentity :: value:Bool -> {result:Bool | result == value} @-}
