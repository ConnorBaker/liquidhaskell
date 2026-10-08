module CallbackRootGood where

{-@ consume :: {g:(b:{Bool | b} -> Bool) | g True} -> Bool @-}
consume :: (Bool -> Bool) -> Bool
consume _ = True
