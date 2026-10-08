module ImportedFamilyClient where

import ImportedDataFamily (Family (..), Key)

{-@ reflect extract @-}
extract :: Family Key a -> a
extract (FamilyValue value) = value

{-@ roundTrip :: x:Integer -> {v:Integer | v == x} @-}
roundTrip :: Integer -> Integer
roundTrip value = extract (FamilyValue value)

{-@ reflect extractNested @-}
extractNested :: Family (Maybe Bool) Integer -> Integer
extractNested (NestedFamily value) = value

{-@ nestedRoundTrip :: x:Integer -> {v:Integer | v == x} @-}
nestedRoundTrip :: Integer -> Integer
nestedRoundTrip value = extractNested (NestedFamily value)
