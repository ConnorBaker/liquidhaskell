module KnownInstanceSignedDivGood where

{-@ LIQUID "--ple" @-}

-- Reflected signed quot/rem/div/mod at the known Int and Integer Integral
-- instances, read back with Haskell's rounding (quot/rem truncate, div/mod
-- floor), which differs from the theory's Euclidean division and modulus
-- whenever an operand is negative.
{-@ reflect twice @-}
twice :: Int -> Int
twice x = (x `div` (-2)) `div` (-2)

{-@ reflect dv @-}
dv :: Int -> Int -> Int
dv x y = if y == 0 || y == -1 then 0 else x `div` y

{-@ reflect md @-}
md :: Int -> Int -> Int
md x y = if y == 0 then 0 else x `mod` y

{-@ reflect qt @-}
qt :: Int -> Int -> Int
qt x y = if y == 0 || y == -1 then 0 else x `quot` y

{-@ reflect rm @-}
rm :: Int -> Int -> Int
rm x y = if y == 0 then 0 else x `rem` y

{-@ reflect bigDiv @-}
bigDiv :: Integer -> Integer
bigDiv x = x `div` (-2)

{-@ twiceThree :: {v:() | twice 3 == 1} @-}
twiceThree :: ()
twiceThree = ()

{-@ signs :: {v:() | dv 3 (-2) == -2 && dv (-3) 2 == -2 && dv (-3) (-2) == 1
                  && md 3 (-2) == -1 && md (-3) 2 == 1 && md (-3) (-2) == -1
                  && qt 3 (-2) == -1 && qt (-3) 2 == -1 && qt (-3) (-2) == 1
                  && rm 3 (-2) == 1 && rm (-3) 2 == -1 && rm (-3) (-2) == -1
                  && bigDiv 3 == -2} @-}
signs :: ()
signs = ()

-- Floor division and its modulus reconstruct the dividend.
{-@ reconstruct :: x:Int -> {v:() | (-2) * dv x (-2) + md x (-2) == x} @-}
reconstruct :: Int -> ()
reconstruct _ = ()
