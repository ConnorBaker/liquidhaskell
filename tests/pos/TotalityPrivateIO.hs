module TotalityPrivateIO (action) where

import Control.Exception (evaluate)

action :: IO Int
action = total

-- Ordinary private IO actions must remain verifiable and non-vacuous.
total :: IO Int
total = evaluate 42

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v : Int | 0 < v} @-}
nonVacuity :: Int -> Int
nonVacuity n = n - 1
