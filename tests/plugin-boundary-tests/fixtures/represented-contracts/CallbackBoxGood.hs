module CallbackBoxGood where

data Box a = Box {unBox :: a}

{-@ measure unBox @-}

{-@ consume :: {h:Box (b:{Bool | b} -> Bool) | unBox h True} -> Bool @-}
consume :: Box (Bool -> Bool) -> Bool
consume _ = True
