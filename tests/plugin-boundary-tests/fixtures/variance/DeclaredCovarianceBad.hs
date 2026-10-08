module DeclaredCovarianceBad where

data Negative a = Negative (a -> Int)

{-@ data variance Negative covariant @-}
