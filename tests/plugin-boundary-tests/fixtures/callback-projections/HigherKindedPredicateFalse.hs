{-# LANGUAGE NoImplicitPrelude #-}
module HigherKindedPredicateFalse where

import GHC.Types (Bool)

{-@ bad :: (forall<p :: Bool -> Bool>. f Bool<p> -> Bool<p>) -> f Bool -> {v:Bool | false} @-}
bad :: (f Bool -> Bool) -> f Bool -> Bool
bad selector container = selector container
