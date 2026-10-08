module DictionaryTerminationGood where

data Input = Stop | More Input

{-@ autosize Input @-}

class Predicate a where
    predicate :: a -> Bool

instance Predicate Input where
    predicate = walk

walk :: Input -> Bool
walk Stop = False
walk (More child) = predicate child
