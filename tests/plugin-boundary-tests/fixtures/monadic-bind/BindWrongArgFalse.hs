module BindWrongArgFalse where

import Control.Monad.Trans.State.Strict (State, get)

-- The bound value is an IO action, but the monad is State, not IO.
-- evalState getAct (pure 5) is an action that returns 5.
{-@ getAct :: State (IO Int) (IO {v:Int | v < 0}) @-}
getAct :: State (IO Int) (IO Int)
getAct = do
  act <- get
  pure act
