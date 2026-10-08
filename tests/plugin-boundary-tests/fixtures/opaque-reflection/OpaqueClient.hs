module OpaqueClient where

import OpaqueProducer (importedF)

{-@ opaque-reflect importedF @-}
{-@ q :: x:Integer -> {v:Integer | v == importedF x} @-}
q :: Integer -> Integer
q x = importedF x
