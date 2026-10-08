module CallbackClientFalse where

import CallbackProducer (Callback, produce)

-- Demand the same imported field contract before the independent counterclaim.
{-@ wrap :: function:((Int -> Int) -> Int) -> {v:Callback | callbackFunction v == function} @-}
wrap :: ((Int -> Int) -> Int) -> Callback
wrap function = produce function

-- A retained higher-order selector must not make scalar checks vacuous.
{-@ wrong :: {v:Int | v == 1} @-}
wrong :: Int
wrong = 0
