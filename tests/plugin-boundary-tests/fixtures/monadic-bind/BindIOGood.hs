module BindIOGood where

{-@ posIO :: IO {v:Int | 0 < v && v < 100} @-}
posIO :: IO Int
posIO = pure 5

-- The bound value's refinement reaches the continuation.
{-@ ioGood :: IO {v:Int | 1 < v && v <= 100} @-}
ioGood :: IO Int
ioGood = do
  x <- posIO
  pure (x + 1)
