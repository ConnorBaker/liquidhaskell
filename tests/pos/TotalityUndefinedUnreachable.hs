module TotalityUndefinedUnreachable (onlyFalse, impossible) where

{-@ onlyFalse :: x:{v:Bool | not v} -> Int @-}
onlyFalse :: Bool -> Int
onlyFalse x = if x then undefined else 0

{-@ impossible :: {v:Int | false} -> Int @-}
impossible :: Int -> Int
impossible _ = undefined

{-@ fail nonVacuity @-}
{-@ nonVacuity :: {v:Bool | v} @-}
nonVacuity :: Bool
nonVacuity = False
