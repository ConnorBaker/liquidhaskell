module ReturnedCallbackGood (f) where

{-@ f :: Integer -> {v:Integer | v == 0} @-}
f :: Integer -> Integer
f _ = 0

{-@ firstOnly :: xs:{[Integer] | len xs > 0} -> Integer @-}
firstOnly :: [Integer] -> Integer
firstOnly (x : _) = x

{-@ fail privateProbe @-}
{-@ privateProbe :: {v:[(xs:{[Integer] | len xs > 0} -> Integer)] | False} @-}
privateProbe :: [[Integer] -> Integer]
privateProbe = [firstOnly]
