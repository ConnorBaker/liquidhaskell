module GroupFailuresExpectedSafe where

-- An expected failure that verifies, checked after both failing groups it
-- depends on, is still reported.
{-@ need :: {v:Int | v > 0} -> Int @-}
need :: Int -> Int
need x = x

first :: Int -> Int
first a = need a

second :: Int -> Int
second b = need b

{-@ fail okay @-}
{-@ okay :: Int -> Int @-}
okay :: Int -> Int
okay c = second (first c)
