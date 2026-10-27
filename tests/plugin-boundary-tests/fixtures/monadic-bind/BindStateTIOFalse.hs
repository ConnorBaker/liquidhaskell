module BindStateTIOFalse where

import Control.Monad.Trans.State.Strict (StateT, get)

-- evalStateT getNegIO 5 == 5: StateT over IO is not IO.
{-@ getNegIO :: StateT Int IO {v:Int | v < 0} @-}
getNegIO :: StateT Int IO Int
getNegIO = do
  n <- get
  pure n
