module EnumIntToWordGood (natural, negative) where

import GHC.Internal.Enum (enumIntToWord)

{-@ natural :: x:{Int | 0 <= x} -> {v:Word | v == x} @-}
natural :: Int -> Word
natural x = enumIntToWord x

{-@ negative :: x:{Int | x < 0} -> {v:Word | v > 9223372036854775807} @-}
negative :: Int -> Word
negative x = enumIntToWord x
