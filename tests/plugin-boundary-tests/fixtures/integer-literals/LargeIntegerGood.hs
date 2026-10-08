{-# LANGUAGE NegativeLiterals #-}

module LargeIntegerGood where

{-@ positive :: {v:Integer | v = 1361129467683753853853498429727072845824} @-}
positive :: Integer
positive = 1361129467683753853853498429727072845824

{-@ negative :: {v:Integer | v = -1361129467683753853853498429727072845824} @-}
negative :: Integer
negative = -1361129467683753853853498429727072845824

{-@ reflect choose @-}
choose :: Bool -> Integer
choose flag = if flag then 18446744073709551615 else -18446744073709551615

{-@ reflectedPositive :: {v:Integer | v = 18446744073709551615} @-}
reflectedPositive :: Integer
reflectedPositive = choose True

{-@ reflectedNegative :: {v:Integer | v = -18446744073709551615} @-}
reflectedNegative :: Integer
reflectedNegative = choose False
