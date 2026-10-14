module GroupFailuresAuthoredResult where

-- `positive` rejects its authored result. Its consumer `use` holds under that
-- authored signature; `bad` fails under any view of `positive`.
{-@ need :: {v:Int | v > 0} -> Int @-}
need :: Int -> Int
need x = x

{-@ positive :: Int -> {v:Int | v > 0} @-}
positive :: Int -> Int
positive x = x

use :: Int -> Int
use y = need (positive y)

bad :: Int -> Int
bad z = need (positive z - 1)
