module MeasureSourceNameFalse where

{-@ measure nonEmpty :: [k] -> Bool
      nonEmpty ([])   = false
      nonEmpty (x:xs) = true
@-}

{-@ nonEmpty :: (Ord k) => xs:[k] -> {v:Bool | v <=> nonEmpty xs} @-}
nonEmpty :: (Ord k) => [k] -> Bool
nonEmpty []    = False
nonEmpty (_:_) = True

{-@ none :: {v:[Int] | nonEmpty v} @-}
none :: [Int]
none = []
