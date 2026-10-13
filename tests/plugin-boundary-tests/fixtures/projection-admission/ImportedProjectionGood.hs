{-# LANGUAGE NoImplicitPrelude #-}
module ImportedProjectionGood where

import GHC.Tuple (Solo (MkSolo))
import GHC.Types (Bool, Int)

-- No declaration or source match here gives MkSolo a logical selector, so
-- this projection remains its own measure rather than a selector application.
{-@ measure unsolo :: Solo Int -> Int
      unsolo (MkSolo x) = x
  @-}

{-@ assume opaque :: s:Solo Int -> {v:Int | v = unsolo s} @-}
opaque :: Solo Int -> Int
opaque _ = 0

{-@ copy :: s:Solo Int -> {v:Int | v = unsolo s} @-}
copy :: Solo Int -> Int
copy s = opaque s
