{-# LANGUAGE NoImplicitPrelude #-}

module ImportedCarrier (Pick (..)) where

import GHC.Types (Int)

class Pick a where
    pick :: a -> a
    other :: a -> a

instance Pick Int where
    pick x = x
    other x = x
