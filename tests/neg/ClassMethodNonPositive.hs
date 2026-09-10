{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module ClassMethodNonPositive where

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

invalidCall :: Unit
invalidCall = many (0 :: Int) Unit

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x - 1
