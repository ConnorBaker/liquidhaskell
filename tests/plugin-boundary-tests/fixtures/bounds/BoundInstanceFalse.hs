module BoundInstanceFalse where

-- The bound is instantiated over the integers in scope at each subtyping
-- check, including the checked value itself.
{-@ next :: forall <q :: Integer -> Bool>.
           {x::Integer<q> |- {v:Integer | v = x + 1} <: Integer<q>}
           x:Integer<q> -> Integer<q> @-}
next :: Integer -> Integer
next x = x + 2
