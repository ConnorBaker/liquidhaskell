module ConstructGood where

import Plain
import PlainDependent

-- Constructing P gives its constructor's measure fact, without PLE.
{-@ mk :: x:Int -> {v:P | getP v == x} @-}
mk :: Int -> P
mk x = P x
