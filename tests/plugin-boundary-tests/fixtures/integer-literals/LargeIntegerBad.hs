{-# LANGUAGE NegativeLiterals #-}

module LargeIntegerBad where

{-@ wrongPositive :: {v:Integer | v = 1361129467683753853853498429727072845825} @-}
wrongPositive :: Integer
wrongPositive = 1361129467683753853853498429727072845824
