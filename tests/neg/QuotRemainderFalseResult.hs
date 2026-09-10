{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
module QuotRemainderFalseResult where

{-@ invalid :: Integer -> {v:Integer | false} @-}
invalid :: Integer -> Integer
invalid x = if snd (quotRem x (-3)) >= 0 then 42 else 43

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x
