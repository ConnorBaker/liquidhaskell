module NativeCarrierDatatypeFormation where

data LeftCarrier = LeftValue
data RightCarrier = RightValue

{-@ witness :: x:LeftCarrier -> y:RightCarrier
            -> {v:() | (x ~~ y) => (y ~~ x)} @-}
witness :: LeftCarrier -> RightCarrier -> ()
witness _ _ = ()
