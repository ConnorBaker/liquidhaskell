module ProjectionSharingGood where

data Box a = Box a

{-@ measure field :: Box a -> a
      field (Box x) = x @-}

{-@ instantiated :: n:Integer -> flag:Bool
      -> {v:Bool | field (Box n) == n && field (Box flag) == flag => v} @-}
instantiated :: Integer -> Bool -> Bool
instantiated _ _ = True

{-@ refined :: positive:{v:Integer | v > 0} -> negative:{v:Integer | v < 0}
      -> {v:Bool | field (Box positive) > 0 && field (Box negative) < 0 => v} @-}
refined :: Integer -> Integer -> Bool
refined _ _ = True

{-@ callbacks :: positive:(Box ({v:Int | v > 0} -> {v:Int | v >= 0})
                         -> ({v:Int | v > 0} -> {v:Int | v >= 0}))
              -> negative:(Box ({v:Int | v < 0} -> {v:Int | v <= 0})
                         -> ({v:Int | v < 0} -> {v:Int | v <= 0}))
              -> {v:Bool | positive == field && negative == field => v} @-}
callbacks :: (Box (Int -> Int) -> Int -> Int) -> (Box (Int -> Int) -> Int -> Int) -> Bool
callbacks _ _ = True

data Choice a = Empty | Full a

{-@ measure selected :: Choice a -> a
      selected (Full x) = x @-}

-- Applying a partial projector to a known constructor is distinct from
-- claiming that its unrestricted first-class arrow is total.
{-@ guarded :: left:Integer -> right:Integer
      -> {v:Bool | selected (Full left) == left && selected (Full right) == right => v} @-}
guarded :: Integer -> Integer -> Bool
guarded _ _ = True
