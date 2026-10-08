module FixedWidthFirstClassFalse where

import Data.Word (Word64)

{-@ add :: x:Word64 -> y:Word64 -> {v:Word64 | v = x + y} @-}
add :: Word64 -> Word64 -> Word64
add = (+)

{-@ convert :: x:Integer -> {v:Word64 | v = x} @-}
convert :: Integer -> Word64
convert = fromInteger
