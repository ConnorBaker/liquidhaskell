module DictionaryValueFieldGood where

class Value a where
    optional :: Maybe a
    decide :: a -> Bool

instance Value Bool where
    optional = Nothing
    decide True = True
    decide False = case (optional :: Maybe Bool) of
        Nothing -> False
        Just value -> value
