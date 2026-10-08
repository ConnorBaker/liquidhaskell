module ImportedNestedFamilyFalse where

import ImportedDataFamily (Family (..))

{-@ extract :: Family (Maybe Bool) Integer -> {v:Integer | False} @-}
extract :: Family (Maybe Bool) Integer -> Integer
extract (NestedFamily value) = value
