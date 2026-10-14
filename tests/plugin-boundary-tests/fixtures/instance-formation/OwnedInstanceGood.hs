{-# LANGUAGE NoImplicitPrelude #-}

module OwnedInstanceGood (Pick (..)) where

import GHC.Types (Int)

class Pick a where
    pick :: a -> a

{-@ instance Pick Int where
      pick :: x:Int -> {v:Int | v == x} @-}
instance Pick Int where
    pick x = x
