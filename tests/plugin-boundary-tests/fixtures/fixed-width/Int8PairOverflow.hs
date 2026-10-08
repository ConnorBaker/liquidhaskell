module Int8PairOverflow where

import Data.Int (Int8)

bad :: (Int8, Int8)
bad = quotRem (-128 :: Int8) (-1)
