module OwnedFreshNoProof (fresh) where

import OwnedIdentityProvider (ownedIdentity)

{-@ fresh :: value:Bool -> {result:Bool | result == value} @-}
fresh :: Bool -> Bool
fresh = ownedIdentity
