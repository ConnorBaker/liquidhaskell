module BindIODepGood where

{-@ posIO :: IO {v:Int | 0 < v && v < 100} @-}
posIO :: IO Int
posIO = pure 5

{-@ retI :: z:Int -> IO {v:Int | v == z} @-}
retI :: Int -> IO Int
retI z = pure z

-- The continuation's result type names the bound x.
{-@ depGood :: IO {v:Int | 0 < v} @-}
depGood :: IO Int
depGood = do
  x <- posIO
  retI x
