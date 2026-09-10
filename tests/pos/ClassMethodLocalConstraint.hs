{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module ClassMethodLocalConstraint where

class C a where
    one :: a -> a
    many :: (Integral b) => b -> a -> a

{-@ class C a where
      one :: a -> a
      many :: forall b. Integral b => {n:b | n > 0} -> x:a -> {v:a | v == x}
  @-}

data Unit = Unit

instance C Unit where
    one x = x
    many _ x = x

validCall :: Unit
validCall = many (1 :: Int) Unit

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x - 1
