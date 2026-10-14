-- Num Int's contracts include a nonlinear product; passing the dictionary to a
-- polymorphic function must stay valid (and cheap) at any Int instantiation.
module NumPolyIntGood (g) where

{-@ keep :: Num a => a -> a @-}
keep :: Num a => a -> a
keep x = x
{-# NOINLINE keep #-}

{-@ g :: Int -> Int @-}
g :: Int -> Int
g x = keep x
