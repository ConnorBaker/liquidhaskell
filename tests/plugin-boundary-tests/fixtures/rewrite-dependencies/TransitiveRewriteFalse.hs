module TransitiveRewriteFalse where

{-@ reflect successor @-}
successor :: Integer -> Integer
successor x = x + 1

{-@ rewrite theorem @-}
{-@ theorem :: x:Integer -> {successor x == x} @-}
theorem :: Integer -> ()
theorem x = middle x

{-@ middle :: x:Integer -> {successor x == x} @-}
middle :: Integer -> ()
middle x = final x

{-@ final :: x:Integer -> {successor x == x} @-}
final :: Integer -> ()
final _ = ()
