module SelectorClientGood where

import SelectorProducer (Box, produce)

-- The imported projection must read the producer's declared field selector.
{-@ wrap :: value:Int -> {v:Box | unbox v == value} @-}
wrap :: Int -> Box
wrap value = produce value
