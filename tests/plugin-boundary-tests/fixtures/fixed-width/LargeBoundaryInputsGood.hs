module LargeBoundaryInputsGood where

import Data.Int (Int64)
import Data.Word (Word64)

{-@ wrap :: {x:Word64 | x = 18446744073709551615} -> {v:Word64 | v = 0} @-}
wrap :: Word64 -> Word64
wrap x = x + 1

{-@ minimumAbs :: {x:Int64 | x = -9223372036854775808} -> {v:Int64 | v = x} @-}
minimumAbs :: Int64 -> Int64
minimumAbs = abs
