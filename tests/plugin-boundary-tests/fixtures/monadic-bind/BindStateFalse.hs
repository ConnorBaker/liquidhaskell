module BindStateFalse where

import Control.Monad.Trans.State.Strict (State, get, put)

-- execState decr 0 == -1: the bound value is the state, and the bind threads it.
{-@ decr :: State {v:Int | 0 <= v && v < 100} () @-}
decr :: State Int ()
decr = do
  n <- get
  put (n - 1)
