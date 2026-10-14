module KnownInstanceWord8DivGood where

import Data.Word (Word8)

{-@ LIQUID "--reflection" @-}

-- blob-deps-core Hex.lowerHexBytes: reflected Word8 quot/rem at the known
-- Word8 Integral instance feed a refined reflected function.
{-@ reflect digit @-}
{-@ digit :: {n:Word8 | n < 16} -> Word8 @-}
digit :: Word8 -> Word8
digit n = n

{-@ reflect halves @-}
halves :: Word8 -> [Word8]
halves b = [digit (b `quot` 16), digit (b `rem` 16)]
