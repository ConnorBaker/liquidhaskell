module TypedCharLiteralPayloadBad where

{-@ wrong :: {v:Char | v == (lit "not-a-code-point" Char)} @-}
wrong :: Char
wrong = '\0'
