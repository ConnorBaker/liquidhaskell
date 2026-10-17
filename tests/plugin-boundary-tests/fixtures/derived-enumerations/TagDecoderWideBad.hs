{-# LANGUAGE MagicHash #-}
module TagDecoderWideBad (Colour (..), decode) where

import GHC.Exts (Int (I#), tagToEnum#)

data Colour = Red | Green | Blue

{-@ decode :: {v:Int | 0 <= v && v < 4} -> Colour @-}
decode :: Int -> Colour
decode (I# tag) = tagToEnum# tag
