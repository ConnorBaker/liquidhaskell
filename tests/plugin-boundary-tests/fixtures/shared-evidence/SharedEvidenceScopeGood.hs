module SharedEvidenceScopeGood where

import Data.Word (Word8)

{-@ LIQUID "--reflection" @-}

-- The derived instances construct closed dictionaries (Eq (Maybe Int),
-- Ord [Int], ...) that LiquidHaskell shares as top-level evidence. Groups that
-- do not use that evidence must not see it. The reflected comparison keeps a
-- known-instance class method in a refinement alongside the shared evidence.
data P = P {pm :: Maybe Int, pl :: [Int]}
  deriving stock (Eq, Ord, Show)

{-@ seven :: {v:Int | v = 7} @-}
seven :: Int
seven = 7

{-@ reflect lowerHexDigit @-}
{-@ lowerHexDigit :: {nibble:Word8 | nibble < 16}
      -> {byte:Word8 | (48 <= byte && byte <= 57) || (97 <= byte && byte <= 102)} @-}
lowerHexDigit :: Word8 -> Word8
lowerHexDigit nibble
  | nibble < 10 = 48 + nibble
  | otherwise = 87 + nibble
