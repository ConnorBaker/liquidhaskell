{-@ LIQUID "--total-Haskell" @-}
{-@ LIQUID "--check-derived" @-}
module RemainderSigns where

{-@ signedRem :: Integral a => x:a -> y:{v:a | v /= 0} -> {v:a |
      (x >= 0 => v >= 0) && (x <= 0 => v <= 0) &&
      (y > 0 => -y < v && v < y) && (y < 0 => y < v && v < -y)} @-}
signedRem :: (Integral a) => a -> a -> a
signedRem = rem

{-@ signedQuotRem :: Integral a => x:a -> y:{v:a | v /= 0} -> {v:a |
      (x >= 0 => v >= 0) && (x <= 0 => v <= 0) &&
      (y > 0 => -y < v && v < y) && (y < 0 => y < v && v < -y)} @-}
signedQuotRem :: (Integral a) => a -> a -> a
signedQuotRem x y = snd (quotRem x y)

{-@ remPP :: {v:Integer | v == 2} @-}
remPP :: Integer
remPP = rem 5 3

{-@ remNP :: {v:Integer | v == -2} @-}
remNP :: Integer
remNP = rem (-5) 3

{-@ remPN :: {v:Integer | v == 2} @-}
remPN :: Integer
remPN = rem 5 (-3)

{-@ remNN :: {v:Integer | v == -2} @-}
remNN :: Integer
remNN = rem (-5) (-3)

{-@ remZP :: {v:Integer | v == 0} @-}
remZP :: Integer
remZP = rem 0 3

{-@ remZN :: {v:Integer | v == 0} @-}
remZN :: Integer
remZN = rem 0 (-3)

{-@ quotRemPP :: {v:Integer | v == 2} @-}
quotRemPP :: Integer
quotRemPP = snd (quotRem 5 3)

{-@ quotRemNP :: {v:Integer | v == -2} @-}
quotRemNP :: Integer
quotRemNP = snd (quotRem (-5) 3)

{-@ quotRemPN :: {v:Integer | v == 2} @-}
quotRemPN :: Integer
quotRemPN = snd (quotRem 5 (-3))

{-@ quotRemNN :: {v:Integer | v == -2} @-}
quotRemNN :: Integer
quotRemNN = snd (quotRem (-5) (-3))

{-@ quotRemZP :: {v:Integer | v == 0} @-}
quotRemZP :: Integer
quotRemZP = snd (quotRem 0 3)

{-@ quotRemZN :: {v:Integer | v == 0} @-}
quotRemZN :: Integer
quotRemZN = snd (quotRem 0 (-3))

{-@ smallDividend :: {v:Integer | v == -2} @-}
smallDividend :: Integer
smallDividend = rem (-2) 5

{-@ smallDividendNegativeDivisor :: {v:Integer | v == -2} @-}
smallDividendNegativeDivisor :: Integer
smallDividendNegativeDivisor = snd (quotRem (-2) (-5))

{-@ divisible :: {v:Integer | v == 0} @-}
divisible :: Integer
divisible = rem (-6) 3

{-@ divisibleNegativeDivisor :: {v:Integer | v == 0} @-}
divisibleNegativeDivisor :: Integer
divisibleNegativeDivisor = snd (quotRem 6 (-3))

{-@ unitDivisor :: {v:Integer | v == 0} @-}
unitDivisor :: Integer
unitDivisor = rem (-5) 1

{-@ negativeUnitDivisor :: {v:Integer | v == 0} @-}
negativeUnitDivisor :: Integer
negativeUnitDivisor = rem 5 (-1)

{-@ quotientUnitDivisor :: {v:Integer | v == 0} @-}
quotientUnitDivisor :: Integer
quotientUnitDivisor = snd (quotRem (-5) 1)

{-@ quotientNegativeUnitDivisor :: {v:Integer | v == 0} @-}
quotientNegativeUnitDivisor :: Integer
quotientNegativeUnitDivisor = snd (quotRem 5 (-1))

{-@ fail nonVacuity @-}
{-@ nonVacuity :: Int -> {v:Int | v > 0} @-}
nonVacuity :: Int -> Int
nonVacuity x = x
