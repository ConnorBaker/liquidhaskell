{-# LANGUAGE NoImplicitPrelude #-}

module ImportedCallbackCarrier (Apply (..)) where

import GHC.Types (Int)

class Apply a where
    applyCallback :: (a -> a) -> a -> a

instance Apply Int where
    applyCallback callback value = callback value
