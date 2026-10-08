module NominalTermScopeCastBad where

data Token = Token

{-@ embed Token as alpha @-}

{-@ keep :: alpha:Bool -> x:Token -> {v:Token | (v : bool) == (x : bool)} @-}
keep :: Bool -> Token -> Token
keep _ x = x
