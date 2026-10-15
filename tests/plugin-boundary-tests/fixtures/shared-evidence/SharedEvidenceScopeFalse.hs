module SharedEvidenceScopeFalse where

import Data.Word (Word8)

{-@ LIQUID "--reflection" @-}

data P = P {pm :: Maybe Int, pl :: [Int]}
  deriving stock (Eq, Ord, Show)

{-@ reflect lowerHexDigit @-}
{-@ lowerHexDigit :: {nibble:Word8 | nibble < 16}
      -> {byte:Word8 | 48 <= byte && byte <= 57} @-}
lowerHexDigit :: Word8 -> Word8
lowerHexDigit nibble
  | nibble < 10 = 48 + nibble
  | otherwise = 87 + nibble

-- A derived comparison has no contract: its result is not known to hold.
{-@ reflexive :: P -> {v:Bool | v} @-}
reflexive :: P -> Bool
reflexive p = p <= p
