{-# LANGUAGE TypeFamilies #-}

module ImportedDataFamily (Family (..), Key) where

data Key = Key
data family Family tag a
data instance Family Key a = FamilyValue a
data instance Family (Maybe tag) a = NestedFamily a
