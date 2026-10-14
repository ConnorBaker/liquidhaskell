module KnownInstanceWord8Good where

import Data.Word (Word8)

{-@ LIQUID "--reflection" @-}

-- blob-deps-core Hex.lowerHexDigit: reflected Word8 literals and comparisons
-- at the known Word8 instances.
{-@ reflect lowerHexDigit @-}
{-@ lowerHexDigit :: {nibble:Word8 | nibble < 16}
      -> {byte:Word8 | (48 <= byte && byte <= 57) || (97 <= byte && byte <= 102)} @-}
lowerHexDigit :: Word8 -> Word8
lowerHexDigit nibble
  | nibble < 10 = 48 + nibble
  | otherwise = 87 + nibble
