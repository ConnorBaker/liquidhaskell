module DependentNestedBad where

-- The same component is only known to exceed the outer witness.
{-@ outerIntoInner :: (first :: {v:Int | 0 <= v}, ({v:Int | first < v}, Int)) -> {v:Int | 1 < v} @-}
outerIntoInner :: (Int, (Int, Int)) -> Int
outerIntoInner pair = fst (snd pair)
