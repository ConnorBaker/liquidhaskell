module OwnedIgnored (ownedIdentity) where

import OwnedIdentityProvider (ownedIdentity)

{-@ ownedIdentity :: value:Bool -> {result:Bool | result /= value} @-}
{-@ ignore ownedIdentity @-}
