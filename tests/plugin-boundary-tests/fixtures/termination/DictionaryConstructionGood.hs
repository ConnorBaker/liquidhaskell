module DictionaryConstructionGood where

data Input = Input

class Predicate a where
    predicate :: a -> Bool

instance Predicate Input where
    predicate = decide

{-@ decide :: Input -> {v:Bool | not v} @-}
decide :: Input -> Bool
decide _ = False
