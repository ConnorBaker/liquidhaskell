{-# LANGUAGE NoImplicitPrelude #-}
module PartialProjectionGood where

import GHC.Types (Bool, Int)

data Shape = Sized Int | Empty

{-@ measure isSized :: Shape -> Bool
      isSized (Sized n) = true
      isSized Empty = false
  @-}

-- This projection has no complete source case. It remains a declared measure
-- whose only equation is the Sized constructor's refinement.
{-@ measure sizeOf :: Shape -> Int
      sizeOf (Sized n) = n
  @-}

{-@ size :: s:{Shape | isSized s} -> {v:Int | v = sizeOf s} @-}
size :: Shape -> Int
size (Sized n) = n
size Empty = 0
