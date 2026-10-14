module GroupFailuresIndependent where

-- Two independent false call sites in separate proof groups.
{-@ need :: {v:Int | v > 0} -> Int @-}
need :: Int -> Int
need x = x

first :: Int -> Int
first a = need a

second :: Int -> Int
second b = need b
