module NominalTermScopeGood where

data Token = Token

{-@ embed Token as alpha @-}

{-@ keep :: alpha:Bool -> x:Token -> {v:Token | v == x} @-}
keep :: Bool -> Token -> Token
keep _ x = x

{-@ renamed :: other:Bool -> x:Token -> {v:Token | v == x} @-}
renamed :: Bool -> Token -> Token
renamed _ x = x
