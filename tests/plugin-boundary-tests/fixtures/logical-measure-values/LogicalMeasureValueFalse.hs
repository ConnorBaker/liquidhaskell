module LogicalMeasureValueFalse where

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

{-@ reflect applyMeasure @-}
applyMeasure :: ([a] -> Integer) -> [a] -> Integer
applyMeasure observation xs = observation xs

{-@ witness :: xs:[a] -> {v:() | applyMeasure len xs == len xs + 1} @-}
witness :: [a] -> ()
witness _ = ()
