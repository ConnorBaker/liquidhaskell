module TypedCharLiteralCanonicalBad where

{-@ wrong :: {v:Char | v == (lit "00" Char)} @-}
wrong :: Char
wrong = '\0'
