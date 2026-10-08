module MutualRewriteFalse where

{-@ reflect successor @-}
successor :: Integer -> Integer
successor x = x + 1

{-@ rewriteWith first [second] @-}
{-@ first :: xs:[Bool] -> x:Integer -> {successor x == x} @-}
first :: [Bool] -> Integer -> ()
first [] _ = ()
first (_ : xs) x = second xs x

{-@ rewriteWith second [first] @-}
{-@ second :: xs:[Bool] -> x:Integer -> {successor x == x} @-}
second :: [Bool] -> Integer -> ()
second [] _ = ()
second (_ : xs) x = first xs x
