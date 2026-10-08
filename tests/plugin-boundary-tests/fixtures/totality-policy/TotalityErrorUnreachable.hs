{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module TotalityErrorUnreachable where

import GHC.Err (errorWithoutStackTrace)

{-@ guardedError :: {n:Int | n > 0} -> Int @-}
guardedError :: Int -> Int
guardedError n = if n <= 0 then error "unreachable" else n

{-@ guardedStacklessError :: {n:Int | n > 0} -> Int @-}
guardedStacklessError :: Int -> Int
guardedStacklessError n = if n <= 0 then errorWithoutStackTrace "unreachable" else n

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x - 1
