module KnownInstanceWord8False where

import Data.Word (Word8)

{-@ LIQUID "--reflection" @-}

{-@ reflect lowerHexDigit @-}
{-@ lowerHexDigit :: {nibble:Word8 | nibble < 16}
      -> {byte:Word8 | 48 <= byte && byte <= 57} @-}
lowerHexDigit :: Word8 -> Word8
lowerHexDigit nibble
  | nibble < 10 = 48 + nibble
  | otherwise = 87 + nibble
