{-# LANGUAGE ExistentialQuantification #-}

module ExistentialDefaultMeasureGood where

data Package input
  = Empty
  | forall field. (Show field) => Package Bool (input -> field)

{-@ measure isEmpty @-}
isEmpty :: Package input -> Bool
isEmpty Empty = True
isEmpty _ = False
