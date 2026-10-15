module GeneratedHelperPartialProvider (Pick (..), choose) where

class Pick a where
    pick :: a -> a -> Bool

-- As GeneratedHelperProvider, but the generated method is incomplete.
instance Pick Bool where
    {-# NOINLINE pick #-}
    pick value other | value = other

{-# INLINE choose #-}
choose :: Bool -> Bool -> Bool
choose value other = pick value other
