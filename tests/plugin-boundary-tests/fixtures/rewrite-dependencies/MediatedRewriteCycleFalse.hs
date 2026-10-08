module MediatedRewriteCycleFalse where

{-@ reflect successor @-}
successor :: Integer -> Integer
successor x = x + 1

{-@ rewrite first @-}
{-@ first :: x:Integer -> {successor x == x} @-}
first :: Integer -> ()
first x = firstHelper x

{-@ firstHelper :: x:Integer -> {successor x == x} @-}
firstHelper :: Integer -> ()
firstHelper _ = ()

{-@ rewrite second @-}
{-@ second :: x:Integer -> {successor x == x} @-}
second :: Integer -> ()
second x = secondHelper x

{-@ secondHelper :: x:Integer -> {successor x == x} @-}
secondHelper :: Integer -> ()
secondHelper _ = ()
