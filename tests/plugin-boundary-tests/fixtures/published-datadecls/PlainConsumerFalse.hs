{-@ LIQUID "--ple" @-}
module PlainConsumerFalse where

import Plain
import PlainDependent

{-@ field :: n:Int -> {v:Int | v == usesP (P n)} @-}
field :: Int -> Int
field n = n + 2
