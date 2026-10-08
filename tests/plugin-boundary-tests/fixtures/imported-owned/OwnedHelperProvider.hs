module OwnedHelperProvider (ownedNested, hydratedHelper) where

{-# INLINE ownedNested #-}
ownedNested :: Bool -> Bool
ownedNested value = hydratedHelper value

{-# NOINLINE hydratedHelper #-}
hydratedHelper :: Bool -> Bool
hydratedHelper value = value
