module BindEitherLeftFalse where

-- bindLeft (Left (-1)) == Left (-1): the bind short-circuits with the input's
-- Left, whose payload this contract does not bound.
{-@ bindLeft :: Either Int Int -> Either {v:Int | v > 0} Int @-}
bindLeft :: Either Int Int -> Either Int Int
bindLeft e = do
  x <- e
  Right x
