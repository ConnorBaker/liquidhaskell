module MeasureDomainGood where

{-@ measure left @-}
{-@ left :: flag:{Bool | flag} -> {v:Integer | right flag == right flag} @-}
left :: Bool -> Integer
left False = 0
left True = 0

{-@ measure right @-}
{-@ right :: flag:{Bool | flag} -> {v:Integer | v == left flag} @-}
right :: Bool -> Integer
right True = 0
