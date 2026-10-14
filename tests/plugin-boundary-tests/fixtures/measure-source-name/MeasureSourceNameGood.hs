module MeasureSourceNameGood where

-- An authored measure and a same-spelled source function (liquid-prelude's
-- Bag.fromList pattern). Resolution names the measure in refinements; the
-- source function's dictionary is not part of the measure's sort.
{-@ measure nonEmpty :: [k] -> Bool
      nonEmpty ([])   = false
      nonEmpty (x:xs) = true
@-}

{-@ nonEmpty :: (Ord k) => xs:[k] -> {v:Bool | v <=> nonEmpty xs} @-}
nonEmpty :: (Ord k) => [k] -> Bool
nonEmpty []    = False
nonEmpty (_:_) = True

-- No Ord dictionary is in scope here: only the measure can be meant.
{-@ assume headOr :: k -> {xs:[k] | nonEmpty xs} -> k @-}
headOr :: k -> [k] -> k
headOr _ (x:_) = x
headOr d []    = d

{-@ two :: {v:[Int] | nonEmpty v} @-}
two :: [Int]
two = [1, 2]

{-@ twoNonEmpty :: {v:Bool | v} @-}
twoNonEmpty :: Bool
twoNonEmpty = nonEmpty two
