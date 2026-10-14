{-@ LIQUID "--expect-error-containing=Liquid Type Mismatch" @-}
module LogicalCarrierObservation02 (P (..), wrap, segs, tl) where

import Data.Maybe ()

data P = P [Int]

{-@ measure segs @-}
segs :: P -> [Int]
segs (P xs) = xs

{-@ measure tl @-}
tl :: [Int] -> [Int]
tl [] = []
tl (_ : r) = r

{-@ wrap :: xs:[Int] -> {v:Maybe P | isJust v && len (tl (segs (fromJust v))) == len xs} @-}
wrap :: [Int] -> Maybe P
wrap xs = Just (P xs)
