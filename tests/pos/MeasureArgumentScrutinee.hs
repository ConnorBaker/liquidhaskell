module MeasureArgumentScrutinee where

data Choice = A | B

{-@ measure choiceFlag @-}
choiceFlag :: Choice -> Bool
choiceFlag choice = case choice of
    A -> True
    B -> False

{-@ trueClaim :: {v:() | choiceFlag A} @-}
trueClaim :: ()
trueClaim = ()
