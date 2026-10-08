module LexicalTemplateNamesGood where

{-@ boolIdentity :: x:Bool -> {v:Bool | v == x} @-}
boolIdentity :: Bool -> Bool
boolIdentity x = x

{-@ integerIdentity :: x:Integer -> {v:Integer | v == x} @-}
integerIdentity :: Integer -> Integer
integerIdentity x = x
