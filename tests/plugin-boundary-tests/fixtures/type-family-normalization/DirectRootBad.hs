{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NoImplicitPrelude #-}

module DirectRootBad where

import GHC.Types (Int (I#))

{-@ positive :: {v:Int | v > 0} @-}
positive :: Int
positive = I# 0#
