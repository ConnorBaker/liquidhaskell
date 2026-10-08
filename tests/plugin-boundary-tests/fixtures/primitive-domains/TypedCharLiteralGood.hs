module TypedCharLiteralGood where

{-@ nul :: {v:Char | v == (lit "0" Char)} @-}
nul :: Char
nul = '\0'

{-@ asciiEnd :: {v:Char | v == (lit "127" Char)} @-}
asciiEnd :: Char
asciiEnd = '\127'

{-@ surrogate :: {v:Char | v == (lit "55296" Char)} @-}
surrogate :: Char
surrogate = '\xD800'

{-@ maximumChar :: {v:Char | v == (lit "1114111" Char)} @-}
maximumChar :: Char
maximumChar = '\x10FFFF'

{-@ retain :: c:{Char | (lit "0" Char) <= c && c <= (lit "127" Char)} -> {v:Char | v == c} @-}
retain :: Char -> Char
retain c = c
