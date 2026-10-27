module BindIOFalse where

{-@ posIO :: IO {v:Int | 0 < v && v < 100} @-}
posIO :: IO Int
posIO = pure 5

-- ioOver returns 6.
{-@ ioOver :: IO {v:Int | 6 < v} @-}
ioOver :: IO Int
ioOver = do
  x <- posIO
  pure (x + 1)
