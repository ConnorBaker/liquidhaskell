module LogicalCarrierClient where

import LogicalCarrierGood (Flag (..), Token, echo)

{-@ preserved :: token:Token a -> x:{v:a | v == value token} -> {v:a | v == value token} @-}
preserved :: Token a -> a -> a
preserved token x = echo token x

{-@ flagged :: b:Bool -> {v:Flag | flag v == b} @-}
flagged :: Bool -> Flag
flagged b = Flag b True
