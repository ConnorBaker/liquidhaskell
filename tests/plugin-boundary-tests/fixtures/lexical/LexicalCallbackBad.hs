module LexicalCallbackBad where

{-@ outer :: k:(x:{Bool | x} -> {v:Bool | v}) -> b:Bool -> Bool @-}
outer :: (Bool -> Bool) -> Bool -> Bool
outer k b = go True
  where
    {-@ go :: x:Bool -> {v:Bool | v == k b} @-}
    go :: Bool -> Bool
    go x = if x then k True else k True
