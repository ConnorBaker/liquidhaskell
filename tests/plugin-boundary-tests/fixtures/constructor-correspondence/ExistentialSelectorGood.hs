{-# LANGUAGE ExistentialQuantification #-}

module ExistentialSelectorGood where

data Package input = forall field. (Show field) => Package Bool (input -> field)

packageTag :: Package input -> Bool
packageTag (Package tag _) = tag

{-@ good :: {v:Bool | v} @-}
good :: Bool
good = case Package True (id :: Bool -> Bool) of
    Package tag _ -> tag
