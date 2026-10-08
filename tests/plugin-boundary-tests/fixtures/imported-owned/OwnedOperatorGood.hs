module OwnedOperatorGood ((A..:)) where

import qualified DotColonProvider as A

{-@ (A..:) :: left:Bool -> Bool -> {result:Bool | result == left} @-}
