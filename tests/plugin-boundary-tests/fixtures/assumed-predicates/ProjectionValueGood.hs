module ProjectionValueGood where

{-@ LIQUID "--higherorder" @-}

-- Only complete, selector-backed projections denote their source case.
-- The functional Callback field has a generated selector under --higherorder.

data Box a = Box a

{-@ measure field :: Box a -> a
      field (Box x) = x @-}

{-@ witness :: f:(Box a -> a) -> {v:Bool | f == field => v} @-}
witness :: (Box a -> a) -> Bool
witness _ = True

data Tagged a = Tagged Bool a

{-@ measure tagged :: Tagged a -> Bool
      tagged (Tagged b x) = b @-}
{-@ measure payload :: {v:Tagged a | tagged v} -> a
      payload (Tagged b x) = x @-}

{-@ restricted :: f:({v:Tagged a | tagged v} -> a) -> {v:Bool | f == payload => v} @-}
restricted :: (Tagged a -> a) -> Bool
restricted _ = True

data Callback = Callback (Int -> Int)

{-@ data Callback = Callback { run :: {v:Int | v > 0} -> Int } @-}
{-@ measure action :: Callback -> ({v:Int | v > 0} -> Int)
      action (Callback f) = f @-}

{-@ callback :: f:(Callback -> ({v:Int | v > 0} -> Int)) -> {v:Bool | f == action => v} @-}
callback :: (Callback -> Int -> Int) -> Bool
callback _ = True

{-@ applied :: box:Callback -> f:({v:Int | v > 0} -> Int) -> {v:Bool | f == action box => v} @-}
applied :: Callback -> (Int -> Int) -> Bool
applied _ _ = True
