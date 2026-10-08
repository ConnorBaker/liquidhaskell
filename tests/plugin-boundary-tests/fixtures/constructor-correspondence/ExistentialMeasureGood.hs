{-# LANGUAGE ExistentialQuantification #-}

module ExistentialMeasureGood where

data Package input = forall field. (Show field) => Package Bool (input -> field)

{-@ measure packageTag @-}
packageTag :: Package input -> Bool
packageTag (Package tag _) = tag

{-@ good :: {v:Bool | v} @-}
good :: Bool
good = packageTag (Package True (id :: Bool -> Bool))
