{-# LANGUAGE NoImplicitPrelude #-}

module GuardedImageProducer (A (OnlyA), only) where

import GHC.Types (Bool (True))

data A = OnlyA

{-@ embed A as int @-}

{-@ only :: x:A -> {b:Bool | b && x = OnlyA} @-}
only :: A -> Bool
only OnlyA = True
