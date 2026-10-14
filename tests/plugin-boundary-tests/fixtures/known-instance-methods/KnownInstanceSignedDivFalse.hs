module KnownInstanceSignedDivFalse where

{-@ LIQUID "--ple" @-}

-- Each claim is the theory's Euclidean answer, false for Haskell's rounding.
{-@ reflect dv @-}
dv :: Int -> Int
dv x = x `div` (-2)

{-@ reflect qt @-}
qt :: Int -> Int
qt x = x `quot` 2

{-@ reflect rm @-}
rm :: Integer -> Integer
rm x = x `rem` 2

{-@ divEuclid :: {v:() | dv 3 == -1} @-}
divEuclid :: ()
divEuclid = ()

{-@ quotEuclid :: {v:() | qt (-3) == -2} @-}
quotEuclid :: ()
quotEuclid = ()

{-@ remEuclid :: {v:() | rm (-3) == 1} @-}
remEuclid :: ()
remEuclid = ()
