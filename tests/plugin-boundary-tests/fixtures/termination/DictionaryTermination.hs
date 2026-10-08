module DictionaryTermination where

data Input = Input

class Predicate a where
    predicate :: a -> Bool

instance Predicate Input where
    predicate = loop

loop :: Input -> Bool
loop value = predicate value
