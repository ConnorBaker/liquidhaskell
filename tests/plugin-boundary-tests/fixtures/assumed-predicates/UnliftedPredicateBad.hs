{-# LANGUAGE MagicHash #-}

module UnliftedPredicateBad where

import GHC.Exts (Int#)

{-@ unboxed :: x:Int# -> {v:Int# | v /= x} @-}
unboxed :: Int# -> Int#
unboxed x = x
