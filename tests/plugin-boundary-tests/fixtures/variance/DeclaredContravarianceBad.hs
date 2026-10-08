module DeclaredContravarianceBad where

data Positive a = Positive a

{-@ data variance Positive contravariant @-}
