module ExplicitRewriteCycleFalse where

{-@ reflect successor @-}
successor :: Integer -> Integer
successor x = x + 1

{-@ rewriteWith first [second] @-}
{-@ first :: x:Integer -> {successor x == x} @-}
first :: Integer -> ()
first _ = ()

{-@ rewriteWith second [first] @-}
{-@ second :: x:Integer -> {successor x == x} @-}
second :: Integer -> ()
second _ = ()
