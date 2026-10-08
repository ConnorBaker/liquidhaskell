module TypedCharLiteralFalse where

{-@ wrong :: {v:Char | v == (lit "127" Char)} @-}
wrong :: Char
wrong = '\0'
