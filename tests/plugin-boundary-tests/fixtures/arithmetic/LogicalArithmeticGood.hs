module LogicalArithmeticGood where

{-@ identity :: x:Integer -> {v:Integer | v = x + ((x - x) * (x - x)) + (-x + x) + (0 mod 3) + (0 / 2)} @-}
identity :: Integer -> Integer
identity x = x
