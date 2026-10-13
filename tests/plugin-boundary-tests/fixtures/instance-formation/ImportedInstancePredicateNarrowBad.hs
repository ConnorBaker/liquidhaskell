{-# LANGUAGE NoImplicitPrelude #-}

module ImportedInstancePredicateNarrowBad where

import GHC.Types (Int)

import ImportedCarrier (Pick (..))

{-@ instance Pick Int where
      assume pick :: {v:Int | v > 0} -> Int @-}

{-@ good :: {value:Int | value > 0} -> Int @-}
good :: Int -> Int
good value = pick value
