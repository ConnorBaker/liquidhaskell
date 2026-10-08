{-# LANGUAGE ExistentialQuantification #-}

module ExistentialMeasureBad where

data Package input = forall field. (Show field) => Package Bool (input -> field)

{-@ measure packageTag @-}
packageTag :: Package input -> Bool
packageTag (Package tag _) = tag

{-@ bad :: {v:Bool | v} @-}
bad :: Bool
bad = packageTag (Package False (id :: Bool -> Bool))
