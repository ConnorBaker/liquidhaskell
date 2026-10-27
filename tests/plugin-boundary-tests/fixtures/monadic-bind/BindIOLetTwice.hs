module BindIOLetTwice where

import Data.IORef (IORef, readIORef, writeIORef)

-- next r returns 1, 2, 3, ... from a counter that starts at 0.
{-@ next :: IORef Int -> IO {v:Int | 0 < v} @-}
next :: IORef Int -> IO Int
next r = do
  n <- readIORef r
  writeIORef r (n + 1)
  pure (if 0 <= n && n < 1000 then n + 1 else 1)

{-@ retI :: z:Int -> IO {v:Int | v == z} @-}
retI :: Int -> IO Int
retI z = pure z

-- act runs twice, so a and b come from different runs of next: 1 and 2.
{-@ sameTwice :: IORef Int -> IO {v:Bool | v} @-}
sameTwice :: IORef Int -> IO Bool
sameTwice r = do
  let act = do
        x <- next r
        retI x
  a <- act
  b <- act
  pure (a == b)
