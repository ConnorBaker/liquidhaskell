module ProjectionCallbackBad where

{-@ LIQUID "--higherorder" @-}

data Callback = Callback (Int -> Int)

{-@ data Callback = Callback { run :: {v:Int | v > 0} -> Int } @-}
{-@ measure action :: Callback -> ({v:Int | v > 0} -> Int)
      action (Callback f) = f @-}

{-@ witness :: use:((Callback -> (Int -> Int)) -> Bool) -> {v:Bool | use action} -> Bool @-}
witness :: ((Callback -> Int -> Int) -> Bool) -> Bool -> Bool
witness _ x = x
