module FixedWidthFirstClassGood where

import Data.Word (Word64)

{-@ add :: x:Word64 -> y:Word64 -> {v:Word64 | v = (x + y) mod 18446744073709551616} @-}
add :: Word64 -> Word64 -> Word64
add = (+)

{-@ convert :: x:Integer -> {v:Word64 | v = x mod 18446744073709551616} @-}
convert :: Integer -> Word64
convert = fromInteger
