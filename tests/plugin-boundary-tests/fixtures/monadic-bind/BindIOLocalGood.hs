module BindIOLocalGood where

{-@ posIO :: IO {v:Int | 0 < v && v < 100} @-}
posIO :: IO Int
posIO = pure 5

-- The result template names n, a binder in scope where the bind is.
{-@ addN :: n:{v:Int | 0 <= v && v < 1000} -> IO {v:Int | v > n} @-}
addN :: Int -> IO Int
addN n = do
  x <- posIO
  pure (x + n)
