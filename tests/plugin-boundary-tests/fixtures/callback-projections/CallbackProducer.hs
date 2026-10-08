{-@ LIQUID "--higherorder" @-}

module CallbackProducer (Callback, produce) where

data Callback = Callback ((Int -> Int) -> Int)

-- This structural measure states the logical field equation. The named
-- producer's implementation is checked against the resulting contract.
{-@ measure callbackFunction :: Callback -> ((Int -> Int) -> Int)
      callbackFunction (Callback function) = function
  @-}

{-@ produce :: function:((Int -> Int) -> Int) -> {v:Callback | callbackFunction v == function} @-}
produce :: ((Int -> Int) -> Int) -> Callback
produce function = Callback function
