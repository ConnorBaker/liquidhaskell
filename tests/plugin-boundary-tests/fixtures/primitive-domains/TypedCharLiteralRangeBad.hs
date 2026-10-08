module TypedCharLiteralRangeBad where

{-@ wrong :: {v:Char | v == (lit "1114112" Char)} @-}
wrong :: Char
wrong = '\0'
