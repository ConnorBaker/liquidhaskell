module OwnedQualified (Alias.ownedIdentity) where

import qualified OwnedIdentityProvider as Alias

{-@ Alias.ownedIdentity :: value:Bool -> {result:Bool | result == value} @-}
