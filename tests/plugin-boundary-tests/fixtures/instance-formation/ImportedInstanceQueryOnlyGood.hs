{-# LANGUAGE NoImplicitPrelude #-}

module ImportedInstanceQueryOnlyGood where

import GHC.Types (Int)
import ImportedCarrier (Pick (..))

{-@ instance Pick Int where
      assume pick :: x:Int -> {v:Int | v == x} @-}

{-@ queryOnly :: x:Int -> {v:Int | v == pick x} @-}
queryOnly :: Int -> Int
queryOnly x = x
