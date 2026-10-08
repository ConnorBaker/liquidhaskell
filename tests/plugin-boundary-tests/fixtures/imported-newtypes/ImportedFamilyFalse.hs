module ImportedFamilyFalse where

import ImportedDataFamily (Family (..), Key)

{-@ extract :: Family Key Integer -> {v:Integer | False} @-}
extract :: Family Key Integer -> Integer
extract (FamilyValue value) = value
