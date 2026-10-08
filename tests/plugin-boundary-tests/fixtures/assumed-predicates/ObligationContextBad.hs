module ObligationContextBad where

{-@ assume requiresPositive :: forall <p :: Int -> Bool>. {y::Int<p> |- {v:Int | v == y} <: {v:Int | y > 0}} Int<p> -> Int @-}
requiresPositive :: Int -> Int
requiresPositive x = x

probe :: Int
probe = requiresPositive 0
