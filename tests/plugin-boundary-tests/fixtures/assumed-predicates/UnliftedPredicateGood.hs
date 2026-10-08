{-# LANGUAGE MagicHash #-}

module UnliftedPredicateGood where

import GHC.Exts (Double (D#), Double#, Int (I#), Int#)

{-@ unboxedInt :: x:Int# -> {v:Int# | v == x} @-}
unboxedInt :: Int# -> Int#
unboxedInt x = x

{-@ unboxedDouble :: x:Double# -> {v:Double# | v == x} @-}
unboxedDouble :: Double# -> Double#
unboxedDouble x = x

{-@ boxedInt :: x:Int# -> {v:Int | v == x} @-}
boxedInt :: Int# -> Int
boxedInt x = I# x

{-@ boxedDouble :: x:Double# -> {v:Double | v == (x :: real)} @-}
boxedDouble :: Double# -> Double
boxedDouble x = D# x
