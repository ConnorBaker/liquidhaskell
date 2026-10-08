module PartialContextBad where

{-@ keep :: Eq a => a -> a @-}
keep :: (Eq a, Show a) => a -> a
keep value = value
