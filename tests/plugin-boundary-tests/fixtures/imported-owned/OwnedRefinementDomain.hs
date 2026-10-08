module OwnedRefinementDomain (ownedIdentity) where

import OwnedIdentityProvider (ownedIdentity)

{-@ ownedIdentity :: value:Bool -> {result:Bool | result == value && restricted value == restricted value} @-}

{-@ measure restricted @-}
{-@ restricted :: value:{Bool | value} -> Bool @-}
restricted :: Bool -> Bool
restricted True = True
