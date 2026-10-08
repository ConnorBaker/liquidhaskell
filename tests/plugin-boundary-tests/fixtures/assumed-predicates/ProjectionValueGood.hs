module ProjectionValueGood where

data Box a = Box a

{-@ measure field :: Box a -> a
      field (Box x) = x @-}

{-@ witness :: f:(Box a -> a) -> {v:Bool | f == field => v} @-}
witness :: (Box a -> a) -> Bool
witness _ = True

data Choice a = Empty | Full a

{-@ measure full :: Choice a -> Bool
      full Empty = false
      full (Full x) = true @-}
{-@ measure selected :: {v:Choice a | full v} -> a
      selected (Full x) = x @-}

{-@ restricted :: f:({v:Choice a | full v} -> a) -> {v:Bool | f == selected => v} @-}
restricted :: (Choice a -> a) -> Bool
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
