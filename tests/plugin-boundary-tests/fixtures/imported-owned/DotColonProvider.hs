module DotColonProvider ((.:)) where

{-# INLINE (.:) #-}
(.:) :: Bool -> Bool -> Bool
left .: _right = left
