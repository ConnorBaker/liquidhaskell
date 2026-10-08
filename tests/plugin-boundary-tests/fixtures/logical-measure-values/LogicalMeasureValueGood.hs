module LogicalMeasureValueGood where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

{-@ reflect applyMeasure @-}
applyMeasure :: ([a] -> Integer) -> [a] -> Integer
applyMeasure observation xs = observation xs

{-@ witness :: xs:[a] -> {v:() | applyMeasure len xs == len xs} @-}
witness :: [a] -> ()
witness _ = ()
