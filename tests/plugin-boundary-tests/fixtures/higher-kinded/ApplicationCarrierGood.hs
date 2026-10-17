module ApplicationCarrierGood where

-- A pair's abstract refinement relates its first component to a second
-- component of applied-variable type f a. Matching the pair instantiates that
-- refinement on the applied carrier.

{-@ second :: (c, f a) -> f a @-}
second :: (c, f a) -> f a
second (_, rest) = rest

{-@ firstPositive :: (Int, f a)<{\x y -> 0 < x}> -> {v:Int | 0 < v} @-}
firstPositive :: (Int, f a) -> Int
firstPositive (n, _) = n

-- An unannotated binder generalizes to Foldable t => (c, t b) -> Int.
size (_, values) = length values

{-@ sizePair :: [Int] -> Int @-}
sizePair :: [Int] -> Int
sizePair values = size ((), values)
