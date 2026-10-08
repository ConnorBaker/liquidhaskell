{-# LANGUAGE NegativeLiterals #-}

module LargeIntegerNegativeBad where

{-@ wrongNegative :: {v:Integer | v = 1361129467683753853853498429727072845824} @-}
wrongNegative :: Integer
wrongNegative = -1361129467683753853853498429727072845824
