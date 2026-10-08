module DependentLambdaGood where

{-@ apply :: f:(Integer -> Integer) -> x:Integer -> {v:Integer | v == f x} @-}
apply :: (Integer -> Integer) -> Integer -> Integer
apply function x = function x

-- Identity isolates the enclosing lambda's binder scope from dictionary
-- interpretation; checking the open body would lose the required singleton.
{-@ applyIdentity :: x:Integer -> {v:Integer | v == x} @-}
applyIdentity :: Integer -> Integer
applyIdentity x = apply (\y -> y) x
