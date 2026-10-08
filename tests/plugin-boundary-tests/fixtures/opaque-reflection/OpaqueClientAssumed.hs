module OpaqueClientAssumed where

import OpaqueProducer (importedF)

{-@ opaque-reflect importedF @-}
{-@ assume importedF :: Integer -> Integer @-}
{-@ q :: x:Integer -> {v:Integer | v == importedF x} @-}
q :: Integer -> Integer
q x = importedF x
