{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module ClassMethodImportedSpec (C (..)) where

class C a where
    one :: a -> a
    many :: (Integral b) => b -> a -> a

{-@ class C a where
      one :: a -> a
      many :: forall b. Integral b => {n:b | n > 0} -> a -> a
  @-}

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x - 1
