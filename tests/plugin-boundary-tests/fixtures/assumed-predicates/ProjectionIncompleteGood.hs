module ProjectionIncompleteGood where

data Choice = Empty | Full Int

{-@ measure selected :: Choice -> Int
      selected (Full x) = x @-}

-- An incomplete projection is its own measure, not a source case.
{-@ witness :: f:(Choice -> Int) -> {v:Bool | f == selected => v} @-}
witness :: (Choice -> Int) -> Bool
witness _ = True

{-@ missing :: n:Int -> {v:Bool | selected Empty == n => v} @-}
missing :: Int -> Bool
missing _ = True
