module TransitiveRewriteContractGood where

{-@ reflect successor @-}
{-@ successor :: x:Integer -> {v:Integer | v == x + 1} @-}
successor :: Integer -> Integer
successor x = x + 1

{-@ rewrite theorem @-}
{-@ theorem :: x:Integer -> {successor x == x + 1} @-}
theorem :: Integer -> ()
theorem x = middle x

{-@ middle :: x:Integer -> {successor x == x + 1} @-}
middle :: Integer -> ()
middle x = final x

{-@ final :: x:Integer -> {successor x == x + 1} @-}
final :: Integer -> ()
final x = successor x `seq` ()
