{-@ LIQUID "--ple" @-}
module ViaClientGood where

import Dependent
import Via

-- Unfolding usesW (W n) needs W's selector on the constructor, from W's
-- published data declaration; this module never imports Owner.
{-@ field :: n:Int -> {v:Int | v == usesW (W n)} @-}
field :: Int -> Int
field n = n + 1
