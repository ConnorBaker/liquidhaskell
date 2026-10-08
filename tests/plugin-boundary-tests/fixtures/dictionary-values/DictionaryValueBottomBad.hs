module DictionaryValueBottomBad where

class Value a where
    optional :: Maybe a
    decide :: a -> Bool

instance Value Bool where
    optional = error "invalid value field"
    decide _ = False
