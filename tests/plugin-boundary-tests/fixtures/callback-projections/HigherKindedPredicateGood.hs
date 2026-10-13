{-# LANGUAGE NoImplicitPrelude #-}
module HigherKindedPredicateGood where

import GHC.Types (Bool)

{-@ good :: forall<q :: Bool -> Bool>. (forall<p :: Bool -> Bool>. f Bool<p> -> Bool<p>) -> f Bool<q> -> Bool<q> @-}
good :: (f Bool -> Bool) -> f Bool -> Bool
good selector container = selector container
