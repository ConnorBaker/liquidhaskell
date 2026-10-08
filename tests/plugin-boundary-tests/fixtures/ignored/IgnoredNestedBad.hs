module IgnoredNestedBad where

{-@ ignore ignored @-}
{-@ ignored :: x:Integer -> Integer @-}
ignored :: Integer -> Integer
ignored x = local x
  where
    {-# NOINLINE local #-}
    {-@ local :: y:Integer -> {v:Integer | v == x + y + 1} @-}
    local :: Integer -> Integer
    local y = x + y

{-@ ordinary :: {v:Integer | v == 1} @-}
ordinary :: Integer
ordinary = 0
