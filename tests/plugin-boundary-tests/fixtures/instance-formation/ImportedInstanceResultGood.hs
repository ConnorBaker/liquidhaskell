module ImportedInstanceResultGood where

import ImportedCarrier (Pick (..))

{-@ instance Pick Int where
      assume pick :: x:Int -> {v:Int | v == x} @-}

{-@ good :: {v:Int | v == 0} @-}
good :: Int
good = pick 0
