{-# LANGUAGE NoImplicitPrelude #-}
module HigherKindedPredicateCapability where

import GHC.Types (Bool)

data Identity a = Identity a

{-@ selector :: forall<p :: Bool -> Bool>. Identity Bool<p> -> Bool<p> @-}
selector :: Identity Bool -> Bool
selector (Identity value) = value
