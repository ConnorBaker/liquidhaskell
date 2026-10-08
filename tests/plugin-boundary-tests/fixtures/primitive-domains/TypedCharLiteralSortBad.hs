module TypedCharLiteralSortBad where

{-@ wrong :: {v:Bool | (lit "0" Char) == 0} @-}
wrong :: Bool
wrong = True
