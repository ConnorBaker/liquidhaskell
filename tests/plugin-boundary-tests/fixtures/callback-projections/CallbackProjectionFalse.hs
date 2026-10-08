module CallbackProjectionFalse where

import Data.Coerce (coerce)

-- Match the accepted projection before testing an independent false claim.
newtype Callback = Callback ((Int -> Int) -> Int)

project :: Callback -> (Int -> Int) -> Int
project = coerce

run :: Callback -> Int
run callback = project callback (\x -> x)

{-@ wrong :: {v:Int | v == 1} @-}
wrong :: Int
wrong = 0
