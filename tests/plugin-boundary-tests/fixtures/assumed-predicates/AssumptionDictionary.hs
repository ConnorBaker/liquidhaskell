{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

module AssumptionDictionary where

import GHC.Exts (withDict)

class Choice a where
    choose :: a -> Integer

instance Choice Bool where
    choose _ = 1

{-@ opaque-reflect selected @-}
selected :: (Choice a) => a -> Integer
selected = choose

{-@ assume trusted :: Choice a => x:a -> {v:Integer | v == selected x} @-}
trusted :: (Choice a) => a -> Integer
trusted = selected

other :: Bool -> Integer
other _ = 0

{-@ same :: {v:Integer | v == selected True} @-}
same :: Integer
same = trusted True

{-@ different :: {v:Integer | v == selected True} @-}
different :: Integer
different = withDict @(Choice Bool) other (trusted True)
