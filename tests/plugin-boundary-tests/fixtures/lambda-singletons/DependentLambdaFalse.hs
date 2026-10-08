module DependentLambdaFalse where

{-@ apply :: f:(Integer -> Integer) -> x:Integer -> {v:Integer | v == f x} @-}
apply :: (Integer -> Integer) -> Integer -> Integer
apply function x = function x

-- Identity isolates binder scope from dictionary-dependent source semantics.

{-@ applyIdentity :: x:Integer -> {v:Integer | v == x + 1} @-}
applyIdentity :: Integer -> Integer
applyIdentity x = apply (\y -> y) x
