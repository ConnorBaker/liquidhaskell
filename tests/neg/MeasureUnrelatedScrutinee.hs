module MeasureUnrelatedScrutinee where



data Choice = A | B

opaqueChoice :: Choice
opaqueChoice = B
{-# NOINLINE opaqueChoice #-}

{-@ measure choiceFlag @-}
choiceFlag :: Choice -> Bool
choiceFlag _ = case opaqueChoice of
    A -> True
    B -> False

{-@ falseClaim :: {v:() | choiceFlag A} @-}
falseClaim :: ()
falseClaim = ()
