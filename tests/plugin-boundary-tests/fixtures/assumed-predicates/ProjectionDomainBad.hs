module ProjectionDomainBad where

data Choice a = Empty | Full a

{-@ measure full :: Choice a -> Bool
      full Empty = false
      full (Full x) = true @-}
{-@ measure selected :: {v:Choice a | full v} -> a
      selected (Full x) = x @-}

{-@ witness :: use:((Choice Int -> Int) -> Bool) -> {v:Bool | use selected} -> Bool @-}
witness :: ((Choice Int -> Int) -> Bool) -> Bool -> Bool
witness _ x = x
