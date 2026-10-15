module GeneratedHelperProvider (Pick (..), choose) where

class Pick a where
    pick :: a -> a -> Bool

-- The selected owner's unfolding is the generated binder $fPickBool_$cpick.
-- No branch builds a constructor, which hydration would refuse.
instance Pick Bool where
    {-# NOINLINE pick #-}
    pick value other = value `seq` other

{-# INLINE choose #-}
choose :: Bool -> Bool -> Bool
choose value other = pick value other
