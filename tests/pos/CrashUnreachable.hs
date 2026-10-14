module CrashUnreachable where

import Language.Haskell.Liquid.Prelude (crash)

-- An unreachable call to crash is total.
{-@ clamp :: x:Int -> {v:Int | v >= 0} @-}
clamp :: Int -> Int
clamp x
  | x >= 0 = x
  | x < 0 = 0
  | otherwise = crash False
