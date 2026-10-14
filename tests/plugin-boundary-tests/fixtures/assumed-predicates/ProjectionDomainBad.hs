module ProjectionDomainBad where

data Tagged a = Tagged Bool a

{-@ measure tagged :: Tagged a -> Bool
      tagged (Tagged b x) = b @-}
{-@ measure payload :: {v:Tagged a | tagged v} -> a
      payload (Tagged b x) = x @-}

-- payload is complete and selector-backed, so it denotes its source case.
{-@ witness :: use:((Tagged Int -> Int) -> Bool) -> {v:Bool | use payload} -> Bool @-}
witness :: ((Tagged Int -> Int) -> Bool) -> Bool -> Bool
witness _ x = x
