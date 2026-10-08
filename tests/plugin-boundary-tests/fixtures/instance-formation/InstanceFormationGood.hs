module InstanceFormationGood where

{-@ measure onlyTrue @-}
{-@ onlyTrue :: {flag:Bool | flag} -> Integer @-}
onlyTrue :: Bool -> Integer
onlyTrue True = 0

data Token = Token

class Check a where
    check :: a -> Bool -> Integer
    marker :: a -> Bool

{-@ instance Check Token where
      check :: Token -> flag:Bool -> {value:Integer | flag => onlyTrue flag == onlyTrue flag}
      marker :: Token -> Bool @-}
instance Check Token where
    check _ _ = 0
    marker _ = True
