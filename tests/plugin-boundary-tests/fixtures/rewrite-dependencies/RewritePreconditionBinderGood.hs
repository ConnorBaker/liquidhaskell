module RewritePreconditionBinderGood where

import Prelude hiding (drop, length)

{-@ measure length @-}
{-@ length :: [a] -> {v:Integer | 0 <= v} @-}
length :: [a] -> Integer
length [] = 0
length (_ : xs) = 1 + length xs

{-@ reflect drop @-}
drop :: Integer -> [a] -> [a]
drop _ [] = []
drop n (_ : xs) = if n <= 0 then [] else drop (n - 1) xs

-- The precondition names its value v, not the argument binder xs.
{-@ dropAll :: n:Integer -> xs:{v:[a] | length v <= n} -> { drop n xs == [] } @-}
dropAll :: Integer -> [a] -> ()
dropAll _ [] = ()
dropAll n (_ : xs) = dropAll (n - 1) xs

{-@ rewriteWith dropLength [dropAll] @-}
{-@ dropLength :: ys:[a] -> { drop (length ys) ys == [] } @-}
dropLength :: [a] -> ()
dropLength _ = ()
