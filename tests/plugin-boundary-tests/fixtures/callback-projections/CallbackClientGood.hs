module CallbackClientGood where

import CallbackProducer (Callback, produce)

-- This checked postcondition demands the imported logical field declaration
-- even though the client uses the default first-order checking policy.
{-@ wrap :: function:((Int -> Int) -> Int) -> {v:Callback | callbackFunction v == function} @-}
wrap :: ((Int -> Int) -> Int) -> Callback
wrap function = produce function
