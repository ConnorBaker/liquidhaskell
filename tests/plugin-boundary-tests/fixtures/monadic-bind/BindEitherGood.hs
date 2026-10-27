module BindEitherGood where

-- The input's Left payload passes through; the Right value is bounded.
{-@ keepLeft :: Either {v:Int | v > 0} {v:Int | 0 < v && v < 100} -> Either {v:Int | v > 0} {v:Int | 1 < v && v <= 100} @-}
keepLeft :: Either Int Int -> Either Int Int
keepLeft e = do
  x <- e
  Right (x + 1)
