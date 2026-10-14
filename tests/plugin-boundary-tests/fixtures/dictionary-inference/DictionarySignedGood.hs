module DictionarySignedGood () where

{-@ need :: Monad m => {v:Int | v > 0} -> m Int @-}
need :: Monad m => Int -> m Int
need x = return x

use :: Monad m => m Int
use = need 1
