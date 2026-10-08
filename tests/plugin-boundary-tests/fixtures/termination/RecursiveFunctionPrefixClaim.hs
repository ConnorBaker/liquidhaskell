module RecursiveFunctionPrefixClaim where

{-@ loop :: n:Integer -> {function:(Integer -> Integer) | false} / [n] @-}
loop :: Integer -> Integer -> Integer
loop n =
    let
        {-# NOINLINE partial #-}
        partial = loop n
     in
        \m -> partial m
