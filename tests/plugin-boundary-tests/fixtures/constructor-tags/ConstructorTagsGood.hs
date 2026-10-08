{-# LANGUAGE MagicHash #-}

module ConstructorTagsGood where

import GHC.Exts (Int (I#), dataToTag#)

data Choice = Payload Int | Other Int | Empty | Unused
    deriving (Eq, Ord, Show)

{-@ payloadTag :: Int -> {v:Int | v == 0} @-}
payloadTag :: Int -> Int
payloadTag input = I# (dataToTag# (Payload input))
