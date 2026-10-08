module COffInterpretationBodyBad (cOffToInteger) where

import Data.Int ()
import System.Posix.Types (COff (..))

{-@ measure cOffField :: COff -> Integer
      cOffField (COff value) = value
@-}

{-@ cOffToInteger :: x:COff -> {v:Integer | v == cOffField x} @-}
cOffToInteger :: COff -> Integer
cOffToInteger (COff value) = toInteger value + 1
