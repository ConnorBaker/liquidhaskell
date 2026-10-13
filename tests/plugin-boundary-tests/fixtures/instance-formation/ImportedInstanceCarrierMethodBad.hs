module ImportedInstanceCarrierMethodBad where

import ImportedCarrier (Pick (..))

{-@ instance Pick ({v:Int | v > 0}) where
      assume pick :: {v:Int | v > 1} -> {v:Int | v > 0} @-}

good :: Int
good = pick 2
