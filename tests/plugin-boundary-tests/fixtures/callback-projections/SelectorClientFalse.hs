module SelectorClientFalse where

import SelectorProducer (Box, produce)

-- The same imported field contract rejects a different stored value.
{-@ wrap :: value:Int -> {v:Box | unbox v == value} @-}
wrap :: Int -> Box
wrap value = produce (value + 1)
