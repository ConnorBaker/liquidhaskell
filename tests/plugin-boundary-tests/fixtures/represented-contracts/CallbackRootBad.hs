module CallbackRootBad where

{-@ consume :: {g:(b:{Bool | b} -> Bool) | g False} -> Bool @-}
consume :: (Bool -> Bool) -> Bool
consume _ = True
