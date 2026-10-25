module Consumer where

import Dependent
import Owner

{-@ check :: w:W -> {v:Int | v == wfOf w} @-}
check :: W -> Int
check w = wfOf w
