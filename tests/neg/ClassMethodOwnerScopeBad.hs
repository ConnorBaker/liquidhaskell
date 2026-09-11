{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--eliminate=all" @-}
module ClassMethodOwnerScopeBad where

class Other a where
    stimes :: Int -> a -> a

{-@ class Other a where
      stimes :: {n:Int | n < 0} -> a -> a
  @-}

data Unit = Unit

instance Semigroup Unit where
    Unit <> Unit = Unit

instance Other Unit where
    stimes n x = if n < 0 then error "inside Other's admitted domain" else x

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x - 1
