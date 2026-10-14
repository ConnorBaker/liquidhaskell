module GroupFailuresAuthoredBody where

-- `positive` fails a call site in its own body. Its consumer `use` holds under
-- the authored signature; `bad` fails under any view of `positive`.
{-@ need :: {v:Int | v > 0} -> Int @-}
need :: Int -> Int
need x = x

{-@ positive :: Int -> {v:Int | v > 0} @-}
positive :: Int -> Int
positive x = need x

use :: Int -> Int
use y = need (positive y)

bad :: Int -> Int
bad z = need (positive z - 1)
