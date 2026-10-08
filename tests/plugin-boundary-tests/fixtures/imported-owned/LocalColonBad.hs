module LocalColonBad (outer) where

import DotColonProvider ((.:))

{-@ outer :: value:Bool -> {result:Bool | result == value} @-}
outer :: Bool -> Bool
outer value = value .: value
  where
    {-@ (.:) :: Bool -> right:Bool -> {result:Bool | result == right} @-}
    (.:) :: Bool -> Bool -> Bool
    left .: _right = left
