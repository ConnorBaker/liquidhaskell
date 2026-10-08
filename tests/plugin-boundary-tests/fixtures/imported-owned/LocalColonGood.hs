module LocalColonGood (outer) where

import DotColonProvider ((.:))

{-@ outer :: value:Bool -> {result:Bool | result == value} @-}
outer :: Bool -> Bool
outer value = value .: value
  where
    {-@ (.:) :: left:Bool -> Bool -> {result:Bool | result == left} @-}
    (.:) :: Bool -> Bool -> Bool
    left .: _right = left
