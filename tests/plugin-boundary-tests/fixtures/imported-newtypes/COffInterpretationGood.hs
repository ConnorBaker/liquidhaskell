module COffInterpretationGood (total, positive, negative) where

import Data.Int ()
import System.Posix.Types (COff (..))

{-@ measure cOffField :: COff -> Integer
      cOffField (COff value) = value
@-}

{-@ cOffToInteger :: x:COff -> {v:Integer | v == cOffField x} @-}
cOffToInteger :: COff -> Integer
cOffToInteger (COff value) = toInteger value

{-@ total :: COff -> Integer @-}
total :: COff -> Integer
total = cOffToInteger

{-@ positive :: {v:Integer | v == 37} @-}
positive :: Integer
positive = cOffToInteger (COff 37)

{-@ negative :: {v:Integer | v == -37} @-}
negative :: Integer
negative = cOffToInteger (COff (-37))
