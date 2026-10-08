{-# LANGUAGE ExistentialQuantification #-}

module ExistentialSelectorBad where

data Package input = forall field. (Show field) => Package Bool (input -> field)

packageTag :: Package input -> Bool
packageTag (Package tag _) = tag

{-@ bad :: {v:Bool | v} @-}
bad :: Bool
bad = case Package False (id :: Bool -> Bool) of
    Package tag _ -> tag
