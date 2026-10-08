module OwnedFreshWrong (fresh) where

import OwnedIdentityGood (ownedIdentity)

{-@ fresh :: value:Bool -> {result:Bool | result /= value} @-}
fresh :: Bool -> Bool
fresh = ownedIdentity
