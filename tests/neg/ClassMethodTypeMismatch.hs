{-@ LIQUID "--expect-error-containing=Specified type does not refine Haskell type" @-}
{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module ClassMethodTypeMismatch where

class C a where
    one :: a -> a
    many :: (Integral b) => b -> a -> a

-- Erasing class dictionaries must not erase or swap the real value arguments.
{-@ class C a where
      one :: a -> a
      many :: forall b. Integral b => a -> b -> a
  @-}

data Unit = Unit

instance C Unit where
    one x = x
    many _ x = x
