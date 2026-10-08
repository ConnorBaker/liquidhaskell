module AliasDomainGood where

{-@ total :: Bool -> Bool @-}
total :: Bool -> Bool
total value = value

{-@ restricted :: {value:Bool | value} -> Bool @-}
restricted :: Bool -> Bool
restricted = total

use :: Bool
use = restricted True
