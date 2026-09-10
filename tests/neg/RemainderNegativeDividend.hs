{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
module RemainderNegativeDividend where

{-@ invalid :: {v:Integer | v >= 0} @-}
invalid :: Integer
invalid = rem (-5) 3

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x
