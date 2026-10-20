module MixedOperandsGood where

import Data.Maybe (fromJust, isJust)

{-@ reflect intAgrees @-}
intAgrees :: Int -> Int -> Bool
intAgrees left right = left == right

-- The first argument is a source value; only the second is logical.
{-@ agreesWith :: x:Int -> y:Maybe Int
      -> {v:Bool | v <=> (isJust y && intAgrees x (fromJust y))} @-}
agreesWith :: Int -> Maybe Int -> Bool
agreesWith _ Nothing = False
agreesWith x (Just y) = intAgrees x y
