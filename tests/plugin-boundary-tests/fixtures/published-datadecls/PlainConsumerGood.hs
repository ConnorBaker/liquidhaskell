{-@ LIQUID "--ple" @-}
module PlainConsumerGood where

import Plain
import PlainDependent

-- Unfolding usesP (P n) needs P's selector on the constructor, from the data
-- declaration PlainDependent publishes.
{-@ field :: n:Int -> {v:Int | v == usesP (P n)} @-}
field :: Int -> Int
field n = n + 1
