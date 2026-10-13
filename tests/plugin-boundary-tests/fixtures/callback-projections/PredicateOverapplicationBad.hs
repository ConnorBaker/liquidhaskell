{-# LANGUAGE NoImplicitPrelude #-}

module PredicateOverapplicationBad where

import GHC.Types (Bool)

{-@ bad :: forall<p :: x:Bool -> Bool -> Bool>. x:Bool -> Bool<p x x> @-}
bad :: Bool -> Bool
bad x = x
