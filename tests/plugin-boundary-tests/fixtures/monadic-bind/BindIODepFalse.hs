module BindIODepFalse where

{-@ posIO :: IO {v:Int | 0 < v && v < 100} @-}
posIO :: IO Int
posIO = pure 5

{-@ retI :: z:Int -> IO {v:Int | v == z} @-}
retI :: Int -> IO Int
retI z = pure z

-- depOver returns 5.
{-@ depOver :: IO {v:Int | 6 < v} @-}
depOver :: IO Int
depOver = do
  x <- posIO
  retI x
