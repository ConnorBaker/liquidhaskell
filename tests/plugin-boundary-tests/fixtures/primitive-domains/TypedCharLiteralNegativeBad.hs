module TypedCharLiteralNegativeBad where

{-@ wrong :: {v:Char | v == (lit "-1" Char)} @-}
wrong :: Char
wrong = '\0'
