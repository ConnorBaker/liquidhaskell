{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
module RemainderUnconditionalBounds where

{-@ invalidRem :: Integral a => x:a -> y:{v:a | v /= 0} -> {v:a | v >= 0 && v < y} @-}
invalidRem :: (Integral a) => a -> a -> a
invalidRem = rem

{-@ invalidQuotRem :: Integral a => x:a -> y:{v:a | v /= 0} -> {v:a | v >= 0 && v < y} @-}
invalidQuotRem :: (Integral a) => a -> a -> a
invalidQuotRem x y = snd (quotRem x y)

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x
