module CallbackProjectionGood where

import Data.Coerce (coerce)

-- Without higher-order or ADT checking, this functional field has no
-- generated logical selector. Its representational projection is still total.
newtype Callback = Callback ((Int -> Int) -> Int)

project :: Callback -> (Int -> Int) -> Int
project = coerce

run :: Callback -> Int
run callback = project callback (\x -> x)
