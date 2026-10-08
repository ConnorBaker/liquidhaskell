module DerivedDefaultGood (Choice (..), first, second) where

data Choice = One | Two deriving (Eq, Show)

first :: Choice -> Integer
first choice = requireFirstRange (if choice == One then 0 else 1)

{-@ requireFirstRange :: {v:Integer | 0 <= v && v <= 1} -> Integer @-}
{-# NOINLINE requireFirstRange #-}
requireFirstRange :: Integer -> Integer
requireFirstRange value = value

{-@ second :: Choice -> {v:Integer | 2 <= v && v <= 3} @-}
second :: Choice -> Integer
second choice = if choice == Two then 2 else 3
