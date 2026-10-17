module EnumIntToWordFalse (same) where

import GHC.Internal.Enum (enumIntToWord)

{-@ same :: x:Int -> {v:Word | v == x} @-}
same :: Int -> Word
same x = enumIntToWord x
