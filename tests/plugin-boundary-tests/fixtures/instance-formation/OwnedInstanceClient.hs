{-# LANGUAGE NoImplicitPrelude #-}

module OwnedInstanceClient where

import GHC.Types (Int)
import OwnedInstanceGood (Pick (..))

{-@ same :: x:Int -> {v:Int | v == x} @-}
same :: Int -> Int
same x = pick x
