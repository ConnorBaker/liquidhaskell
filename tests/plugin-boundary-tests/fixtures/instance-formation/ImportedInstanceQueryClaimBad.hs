{-# LANGUAGE NoImplicitPrelude #-}

module ImportedInstanceQueryClaimBad where

import GHC.Types (Int)
import ImportedCarrier (Pick (..))

{-@ instance Pick Int where
      assume pick :: x:Int -> {v:Int | v == x} @-}

{-@ falseClaim :: x:Int -> {v:Int | v /= pick x} @-}
falseClaim :: Int -> Int
falseClaim x = x
