module RefinedOwner (R (..)) where

{-@ data R = R {rf :: {v:Int | 0 <= v}} @-}
data R = R {rf :: Int}
