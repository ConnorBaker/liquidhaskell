module DependentNestedGood where

-- The outer witness refines a component of the inner tuple, below the root
-- of the projected carrier.
{-@ outerIntoInner :: (first :: {v:Int | 0 <= v}, ({v:Int | first < v}, Int)) -> {v:Int | 0 < v} @-}
outerIntoInner :: (Int, (Int, Int)) -> Int
outerIntoInner pair = fst (snd pair)
