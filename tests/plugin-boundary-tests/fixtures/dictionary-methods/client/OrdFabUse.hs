module OrdFabUse (g) where

import OrdFabLib

{-@ g :: {k:K | kv k > 0} -> {k:K | kv k > 0} -> {k:K | kv k > 0} @-}
g :: K -> K -> K
g x y = h x y
