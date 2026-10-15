module KnownInstanceSignedDivFalse where

{-@ LIQUID "--ple" @-}

-- Each claim is the theory's Euclidean answer, false for Haskell's rounding.
-- Proof parameters keep each closed claim from becoming a premise of the others.
{-@ reflect dv @-}
dv :: Int -> Int
dv x = x `div` (-2)

{-@ reflect qt @-}
qt :: Int -> Int
qt x = x `quot` 2

{-@ reflect rm @-}
rm :: Integer -> Integer
rm x = x `rem` 2

{-@ divEuclid :: () -> {v:() | dv 3 == -1} @-}
divEuclid :: () -> ()
divEuclid _ = ()

{-@ quotEuclid :: () -> {v:() | qt (-3) == -2} @-}
quotEuclid :: () -> ()
quotEuclid _ = ()

{-@ remEuclid :: () -> {v:() | rm (-3) == 1} @-}
remEuclid :: () -> ()
remEuclid _ = ()
