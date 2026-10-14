module GroupFailuresSwapped where

-- GroupFailuresIndependent with the two definitions in the other order.
{-@ need :: {v:Int | v > 0} -> Int @-}
need :: Int -> Int
need x = x

second :: Int -> Int
second b = need b

first :: Int -> Int
first a = need a
