{-@ LIQUID "--ple" @-}
module ViaClientFalse where

import Dependent
import Via

{-@ field :: n:Int -> {v:Int | v == usesW (W n)} @-}
field :: Int -> Int
field n = n + 2
