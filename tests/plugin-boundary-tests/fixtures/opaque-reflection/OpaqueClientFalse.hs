module OpaqueClientFalse where

import OpaqueProducer (importedF)

{-@ opaque-reflect importedF @-}
{-@ q :: x:Integer -> {v:Integer | v == importedF x + 1} @-}
q :: Integer -> Integer
q x = importedF x
