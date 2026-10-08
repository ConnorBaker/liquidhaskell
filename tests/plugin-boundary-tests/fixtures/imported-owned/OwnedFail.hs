module OwnedFail (ownedIdentity) where

import OwnedIdentityProvider (ownedIdentity)

{-@ ownedIdentity :: value:Bool -> {result:Bool | result /= value} @-}
{-@ fail ownedIdentity @-}
