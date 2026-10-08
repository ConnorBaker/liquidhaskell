module ProjectionIncompleteBad where

data Choice a = Empty | Full a

{-@ measure selected :: Choice a -> a
      selected (Full x) = x @-}

{-@ witness :: f:(Choice a -> a) -> {v:Bool | f == selected => v} @-}
witness :: (Choice a -> a) -> Bool
witness _ = True
