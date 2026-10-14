module MeasureSourceNameFalse where

{-@ measure evenLen :: [k] -> Bool
      evenLen ([])   = true
      evenLen (x:xs) = not (evenLen xs)
@-}

{-@ evenLen :: (Ord k) => xs:[k] -> {v:Bool | v <=> evenLen xs} @-}
evenLen :: (Ord k) => [k] -> Bool
evenLen []     = True
evenLen (_:xs) = not (evenLen xs)

{-@ one :: {v:[Int] | evenLen v} @-}
one :: [Int]
one = [1]
