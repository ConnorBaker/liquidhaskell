module MeasureSourceNameGood where

-- An authored measure and a same-spelled, recursive source function
-- (liquid-prelude's Bag.fromList pattern). Resolution names the measure in
-- refinements, including in the function's own signature; the source
-- function's Ord dictionary is not part of the measure's sort.
{-@ measure evenLen :: [k] -> Bool
      evenLen ([])   = true
      evenLen (x:xs) = not (evenLen xs)
@-}

{-@ evenLen :: (Ord k) => xs:[k] -> {v:Bool | v <=> evenLen xs} @-}
evenLen :: (Ord k) => [k] -> Bool
evenLen []     = True
evenLen (_:xs) = not (evenLen xs)

-- No Ord dictionary is in scope here: only the measure can be meant.
{-@ assume headOr :: k -> {xs:[k] | not (evenLen xs)} -> k @-}
headOr :: k -> [k] -> k
headOr _ (x:_) = x
headOr d []    = d

{-@ two :: {v:[Int] | evenLen v} @-}
two :: [Int]
two = [1, 2]

{-@ twoEven :: {v:Bool | v} @-}
twoEven :: Bool
twoEven = evenLen two
