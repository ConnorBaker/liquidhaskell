module OwnedOperatorBad ((A..:)) where

import qualified DotColonProvider as A

{-@ (A..:) :: Bool -> right:Bool -> {result:Bool | result == right} @-}
