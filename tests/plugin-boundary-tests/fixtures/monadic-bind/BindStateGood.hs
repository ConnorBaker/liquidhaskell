module BindStateGood where

import Control.Monad.Trans.State.Strict (State, get, put)

-- The state stays in [0, 100).
{-@ incr :: State {v:Int | 0 <= v && v < 100} () @-}
incr :: State Int ()
incr = do
  n <- get
  put (if n < 99 then n + 1 else 0)
